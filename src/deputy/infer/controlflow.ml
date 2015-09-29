(*
 *
 * Copyright (c) 2006, 
 *  Matt Harren        <matth@cs.berkeley.edu>
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * 1. Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
 * 3. The names of the contributors may not be used to endorse or promote
 * products derived from this software without specific prior written
 * permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER
 * OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 *)



(* This file does three things: a call-graph analysis, a points-to
 * analysis of function pointers for the sake of building the call
 * graph, and an analysis of blocking functions in the Linux kernel.
 * 
 * The points-to analysis could be extended to all lvalues, if that
 * were useful.  *)

open Cil
open Pretty
open Dutil

module E = Errormsg
module IH = Inthash
module H = Hashtbl
module DF = Dataflow

open Ptrnode
let (=?) = Util.equals

let verbose = false
let assumeTypesafeFunctionCalls = true

let contextForCall (ftype:typ) (args: exp list): Dattrs.context =
  let _,formals',_,_ = splitFunctionType ftype in
  let formals = argsToList formals' in
  let numFormals = List.length formals in
  let actualsMain, actualsVararg = split args numFormals in

  (* This is a simplified version of the code in dcheck.ml *)
  let ctx = 
    try
      List.fold_right2
        (fun (argName, argType, _) arg ctxAcc ->
          if argName <> "" then
            (Dattrs.addBinding ctxAcc argName (deputyStripCastsForPtrArith arg))
          else
            ctxAcc)
        formals
        actualsMain
        Dattrs.emptyContext
    with Invalid_argument _ ->
      E.s (bug "Expected lists with same length")
  in
  ctx
  

let compileLvalAttribute ctx (annot:attrparam): lval =
  let deps, res = Dattrs.compileAttribute ~deputyAttrsOnly:false ctx annot
  in
  match res with
    Lval lv -> lv
  | _ -> E.s (error "IRQ_SAVE/RESTORE argument must be an lvalue")

                                                                       
(* Function attributes can depend on the parameters.
   Here, take an attribute and compile it with respect to the actual argument. *)
let compileFunctionAttribute (ftype:typ) (args: exp list) ~(reto:lval option)
  (annot:attrparam): lval =
  let ctx = contextForCall ftype args in
  let ctx' = 
    match reto with
      Some lv -> Dattrs.addBinding ctx "__ret" (Lval lv)
    | None -> ctx
  in
  compileLvalAttribute ctx' annot

(****************************************************************************
  **  Part 1:  Points-to analysis for function pointers                     **
  **                                                                        **
  **  Using the graph built by the solver, we push around the set of        **
  **  functions that a node could point to.                                 **
  **                                                                        **
****************************************************************************)

module VarinfoSet =
  Set.Make(struct
    type t = varinfo
    let compare v1 v2 = Pervasives.compare v1.vid v2.vid
  end)


(* The functions to which a node could point. *)
let funcsOfNode: VarinfoSet.t IH.t = IH.create 49

let getFuncs (n: node) : VarinfoSet.t =
  try
    let res = IH.find funcsOfNode n.id in
(*     log "Node %d can point to %a\n" n.id *)
(*       (docList (fun v -> text v.vname)) (VarinfoSet.elements res); *)
    res
  with Not_found ->
(*     log "Node %d currently points nowhere.\n" n.id; *)
    VarinfoSet.empty
    

let doPTA (f: file) : unit = 
  flush !E.logChannel;
  (* The worklist is a set of nodes for whom funcsOfNode has recently 
     changed.*)
  let worklist = Queue.create () in

  (* Step 1: initialize the nodes for the addresses of functions. *)
  let initOneFunc vf : unit = 
    let n = match nodeOfAttrlist vf.vattr with 
        Some n -> n 
      | _ -> E.s (bug "Function %s is missing a node." vf.vname)
    in
    IH.add funcsOfNode n.id (VarinfoSet.singleton vf);
    Queue.add n worklist;
    ()
  in
  iterGlobals f
    (function GFun(fn, _) -> initOneFunc fn.svar
       | GVarDecl(vf,_) when isFunctionType vf.vtype -> initOneFunc vf
       | _ -> () );

  (* Step 2: push stuff around. *)
  while not (Queue.is_empty worklist) do
    let n = Queue.pop worklist in
    let funcs = getFuncs n in

    let considerNode n2: unit =
      (* Ensure (getFuncs n) is a subset of (getFuncs n2) *)
      let funcs2 = getFuncs n2 in
      if not (VarinfoSet.subset funcs funcs2) then begin
        IH.replace funcsOfNode n2.id
          (VarinfoSet.union funcs funcs2);
        Queue.push n2 worklist
      end
    in
 

    (* Successor edges: n-->n2 implies that (getFuncs n) should be a subset
       of (getFuncs n2) *)
    let doSucc e =
      match e.ekind with
        ECast _ 
      | ECompat _ -> considerNode e.eto
      | _ -> ()
    in
    List.iter doSucc n.succ;

    (* For predecessor edges, consider only ECompat edges. *)
    let doPred e =
      match e.ekind with
        ECompat _ -> considerNode e.efrom
      | _ -> ()
    in
    List.iter doPred n.pred
  done;
  ()



(****************************************************************************
 **  Part 2:  Build the flow-insensitive call graph                        **
 ****************************************************************************)

type calltype = Direct | Indirect

(** A call is a function being called and a list of arguments. *)
type call = varinfo * exp list * calltype * location


let d_call () c : doc =
  let vf,args,direct,loc = c in
  dprintf "%s(%a) %a at %a" vf.vname (docList (d_exp ())) args
    insert (if direct= Indirect then text "(Indirect)" else nil)
    d_loc loc


(* A map from each function (using the varinfo id) to 
   the calls that it might makes *)
let callgraph: call list IH.t = IH.create 49

let callgraphLookup (f:varinfo): call list =
  try
    IH.find callgraph f.vid
  with Not_found -> 
    (* Probably an external function *)
    warn "Call graph information has not been computed for function %s"
      f.vname;
    []
    

(* Return the "call" info for this call.
   A direct call returns one item; an indirect may return many *)
let getCalls (f:exp) (args:exp list) (loc:location) : call list =
  match f with
    Lval(Var vf, NoOffset) -> 
      [vf,args,Direct,loc]
  | Lval(Mem pf, NoOffset) when not !Ivyoptions.inferKinds ->
      [] (* We've already warned about this. *)
  | Lval(Mem pf, NoOffset) ->
      let n = match nodeOfAttrlist (typeAttrs (typeOf pf)) with
          Some n -> n
        | n -> E.s (bug "Can't get the node of %a" d_exp pf)
      in
      let funcs = 
        if assumeTypesafeFunctionCalls then begin
          (* Filter the list of functions, considering only those
             who have the same number of formals as we provide
             actuals.  Assume Deputy rules out other cases. *)
          let numActualArgs = List.length args in
          VarinfoSet.filter 
            (fun (f:varinfo) -> 
               match unrollType f.vtype with
                 TFun(_, Some formals, false, _) ->
                   numActualArgs = List.length formals
               | TFun _ -> (* vararg function or no formals specified. *)
                   true (* conservative *)
               | _ -> E.s (bug "expecting TFun"))
            (getFuncs n)
        end
        else
          (getFuncs n)
      in
      let numFuncs = VarinfoSet.cardinal funcs in
      if numFuncs <= 0 && !Ivyoptions.inferKinds then
        warn ("Function pointer %a (node %d) doesn't seem to point to any"
              ^^" functions.\nYou should only use --blocking-analysis with"
              ^^" the whole program.")
          d_exp pf n.id;
      (* If there is exactly one function that pf can point to,
         consider this a direct call. *)
      let isDirect = if numFuncs = 1 then begin
        (* E.log "%a: treating indirect jump as a direct call\n" d_loc loc; *)
        Direct
      end else 
        Indirect
      in
      List.map (fun vf -> (vf,args,isDirect,loc))
        (VarinfoSet.elements funcs)
  | _ -> 
      E.s (bug "Bad Call instruction.")


class findCallsVisitor (funcName: string) (callList: call list ref)
  = object (self)
  inherit nopCilVisitor

  method vinst i =
    (match i with
       Call(_, f, args, loc) -> 
         let addOne c: unit =
           if not (List.mem c !callList) then
             callList := c::!callList
         in
         List.iter addOne (getCalls f args loc)
     | Asm _ | Set _ -> ()
    );
    SkipChildren

  method vexpr e = SkipChildren
  method vtype t = SkipChildren

end

let buildCallGraph (f:file) : unit = 
  if !Ivyoptions.inferKinds then
    doPTA f
  else
    Dutil.warn "Because the whole-file solver was not used, points-to information is unavailable.  Therefore, indirect function calls will be ignored.";

  let doOneFunc (fn: fundec): unit =
    let callList = ref [] in
    let visitor = new findCallsVisitor fn.svar.vname callList in
    ignore(visitCilFunction visitor fn);
   (*  if verbose then *) begin
      E.log "\n%s may call:\n" fn.svar.vname;
      List.iter
        (fun c ->  E.log "   %a\n" d_call c)
        !callList;
    end;
    if IH.mem callgraph fn.svar.vid then
      bug "computed the callgraph twice";
    IH.add callgraph fn.svar.vid !callList
  in
  let doOneGlobal: global -> unit = function
      GFun(fn,_) -> doOneFunc fn
    | _ -> ()
  in
  iterGlobals f doOneGlobal;
  ()

let isLeaf (vf:varinfo): bool =
  try 
    [] = (IH.find callgraph vf.vid)
  with Not_found ->
    E.s (bug "Function %s missing from the call graph." vf.vname)

(* A map from each function (using the varinfo id) to 
   the functions that might call it *)
let buildInversecallgraph (f:file) : fundec list IH.t =
  let inversecallgraph: fundec list IH.t = IH.create (IH.length callgraph) in

  let doOneFunc fn: unit =
    let addCall (c:call): unit =
      let target,_,_,_ = c in
      let oldCallersOfTarget =
        try
          IH.find inversecallgraph target.vid
        with Not_found -> []
      in
      if not (List.memq fn oldCallersOfTarget) then begin
(*         if verbose then *)
(*           E.log "%s calls %s\n" vf.vname target.vname; *)
        IH.replace inversecallgraph target.vid (fn::oldCallersOfTarget)
      end
    in
    List.iter addCall (callgraphLookup fn.svar)
  in
  iterGlobals f
    (function GFun(fn, _) -> doOneFunc fn
       | _ -> () );
  inversecallgraph



(****************************************************************************
 **  Part 3:  A whole-program, flow-sensitive blocking analysis:           **
 ****************************************************************************)

(* Sources of unsoundness:
 *   o IRQ_SAVE/IRQ_RESTORE functions are assumed to do nothing but save/restore.
 *      If they do more than that, the blocking analysis may miss it.
 *   o We don't check for writes that would clobber saved flags. 
 *   o ...
 * *)

type interruptBit = 
    Disabled 
  | Enabled
  | Unchanged
  | UnchangedEnabled (* We have discovered that Unchanged==Enabled on this path *)
  | Top     (* Top *)
  | IrqRestore (* A special placeholder value used to ensure
                  that IRQ_RESTORE functions behave as advertized *)


type whyType = 
  | BlockAnnotation (** Annotated as a blocking function *)
  | JoinWithEnabled of location
      (** The function joins unchanged and enabled, so Unchanged should equal
          Enabled. *)

(* Why did the analysis say that interupts should be enabled? 
   This is one of the reasons above, plus a call chain leading to it. *)
type mustEnable = 
    call list * whyType

(* State of the analysis.
 * For preEnabled, all that matters is the difference between Some and None.
 * The exact contents of preEnabled are only used for error reporting.
 * 
 * Locally:
 * This is a lattice where the top element is 
 *  { interruptState = Top; precondition = Some _; savedFlags = [] }
 * 
 * Interprocedurally:
 * Top isn't used (we just report an error and save Unchanged in the summary).
 * savedFlags is also unused. Therefore the top element is
 *  { interruptState = Unchanged; preEnabled = Some _; }
 * Also, preEnabled is ignored if there's a BLOCKING annotation on the function.
 * 
 *)
type blockingState = {
  interruptState: interruptBit; (* Postcondition *)
  precondition: mustEnable option; (* If a blocking function might be called without
                           first enabling interrupts, this is a call chain
                           demonstrating that. *)
  savedFlags: (lval * interruptBit) list;
}


let d_bit (): interruptBit -> doc =
  (function Disabled -> text "disabled" 
     | Enabled -> text "enabled"
     | Unchanged -> text "unchanged"
     | UnchangedEnabled -> text "unchanged, but enabled"
     | IrqRestore -> text "restore_saved_flags"
     | Top -> text "Top")
let d_blockingState () s : doc =
  (if s.precondition <> None then
    text "May block; "
  else nil)
  ++
  d_bit () s.interruptState
  ++ text "; " ++
  docList ~sep:(text "::") 
    (fun (lv,b) -> dprintf "(%a -> %a)" d_lval lv d_bit b)
    ()
    s.savedFlags

let d_whyType (): whyType -> doc = function
    BlockAnnotation -> text "which is annotated as blocking"
  | JoinWithEnabled loc ->
      text "which enables interrupts along only one path at "
      ++ d_loc () loc
      

(* The state/summary of a function that does nothing *)
let emptySummary =
  { interruptState = Unchanged;
    precondition = None;
    savedFlags = [] }

(* Merge two precondition values.  If both could block, choose the best
   (e.g shortest) of them *)
let shorter r1 r2 =
  let (l1,wt1) = r1 in
  let (l2,wt2) = r2 in
  (* return the shorter list.  
     But give priority to annotations over bad joins *)
  if wt1 = wt2 then begin
    if (List.length l1) <= (List.length l2) then r1 else r2
  end 
  else if wt1 = BlockAnnotation then r1 else r2
let betterMayBlock mb1 mb2 =
  match mb1, mb2 with
    None, None -> None
  | Some l1, Some l2 -> Some (shorter l1 l2)
  | Some l, None
  | None, Some l -> Some l


(****************************************************************************
 **  Part 3.1:  Blocking annotations and stuff                             **
 ****************************************************************************)

let assertIntsEnabledFun = "__deputyAssertIntEnabled"

class blockingPrinterClass : descriptiveCilPrinter = object (self)
  inherit Dattrs.deputyPrinterClass ~showBounds:true ~enable:false as super

  method pAttr (Attr (an, args) : attribute) : doc * bool =
    match an, args with 
    | ("blocking"), [] ->
        text "BLOCKING", false
    | ("noblocking"), [] ->
        text "NOBLOCKING", false
    | "blockingunless", [AInt arg; AInt mask] ->
        dprintf "BLOCKINGUNLESS(%d,%d)" arg mask, false
    | _ ->
        super#pAttr (Attr (an, args))
end


(* Does Callee block?  If so, change the precondition field of state to Some [] *)
let handleBlockingAnnotations summary 
  ~(curstate:interruptBit) ~(caller:varinfo) ~(call:call)
  : blockingState =
  let callee, args, _, _ = call in
  let alwaysBlocks () = 
    {summary with precondition = Some ([], BlockAnnotation)}
  in
  let neverBlocks () = 
    {summary with precondition = None}
  in
  let conditionallyBlocks () = 
    (* Calls e.g. kmalloc with a variable flags argument,
       and the caller has a blockingunless annotation.
       FIXME: UNSOUND: make sure this is the same arg that was
       passed to the caller. *)
    match curstate with
      Enabled | Unchanged | UnchangedEnabled -> summary
    | Disabled | Top ->
        Dutil.warn "%s called with a variable flags argument when interrupts might be disabled." callee.vname;
        alwaysBlocks ()
    | IrqRestore -> E.s (unimp "call a conditionally-blocking function from an IRQ_RESTORE function.")

  in
  if (hasAttribute "blocking" callee.vattr) then
    alwaysBlocks ()
  else if (hasAttribute "noblocking" callee.vattr) then
    neverBlocks ()
  else match filterAttributes "blockingunless" callee.vattr with
    [] ->
      (* There is no annotation *)
      summary
  | [Attr("blockingunless", [AInt arg; AInt mask])] -> begin
      let value: exp = 
        try
          List.nth args (arg-1)
        with Failure _ -> 
          E.s (Dutil.bug "too few args in call to %s" callee.vname)
      in
      (* The function blocks if (value&mask) is zero *)
      match isInteger (constFold true value) with
        Some value' ->
          let blocks = 0 = ((i64_to_int value') land mask) in
          if blocks then begin
            (* Dutil.log "call to %s blocks here." vf.vname; *)
            alwaysBlocks ()
          end
          else begin
            (* Dutil.log "call to %s is non-blocking." vf.vname; *)
            neverBlocks ()
          end
      | None -> 
          (* The flags argument is a variable *)
          if not (hasAttribute "blockingunless" caller.vattr) then begin
            Dutil.warn "%s called with a variable flags argument." 
              callee.vname;
            alwaysBlocks ()
          end else
            conditionallyBlocks ()
    end
  | _ -> E.s (Dutil.error "Bad BLOCKINGUNLESS attr")


(****************************************************************************
 **  Part 3.2:  The rest of the analysis                                   **
 ****************************************************************************)

let curFunc = ref Cil.dummyFunDec
let curFuncSummary : blockingState option ref = ref None
let functionSummaries: (blockingState * int) IH.t = IH.create 50

(* A list of places that call blocking functions after explicitly disabling
   interrupts *)
let blockingErrors: ((location*fundec*interruptBit), mustEnable) H.t = 
  H.create 10

exception AddPrecondition of mustEnable

(********* Functions that update the state ********)
let enableInterrupts s : blockingState =
  {s with interruptState = Enabled}
let disableInterrupts s : blockingState =
  {s with interruptState = Disabled}

let assertInterruptsEnabled calleename s : blockingState =
  match s.interruptState with
    Enabled | UnchangedEnabled -> s
  | Unchanged -> { s with interruptState = UnchangedEnabled }
  | Disabled ->
      error "Call to %s will always fail." calleename;
      { s with interruptState = Enabled }
  | Top -> { s with interruptState = Enabled }
  | IrqRestore -> 
      (* E.s (unimp "Call to %s in an IRQ_RESTORE function" calleename) *)
      s


let restoreInterrupts s lv : blockingState =
  try 
    {s with interruptState = List.assoc lv s.savedFlags}
  with Not_found ->
    Dutil.warn "Blocking error: restoring the interrupt state from %a, which I don't recognize.  State is \"%a\""
    d_lval lv d_blockingState s;
    {s with interruptState = Top}
let saveInterrupts s lv : blockingState =
  if List.mem (lv,s.interruptState) s.savedFlags then
    s (* nothing to do *)
  else begin
    (* Delete any previous bindings for lv *)
    let different (lv',_) = not (lv' =? lv) in
    let others = 
      if List.for_all different s.savedFlags then s.savedFlags
      else List.filter different s.savedFlags 
    in
    { s with savedFlags = (lv,s.interruptState)::others }
  end

(* Handle the precondition part of summary. *)
let callFunctionHandleMayBlock s call : blockingState =
  let (f:varinfo),_,_,_ = call in
  let summary,_ = 
    try
      IH.find functionSummaries f.vid
    with Not_found ->
      emptySummary,0
  in
  (* If there are BLOCKING or NOBLOCKING annotations, those take precedence *)
  let summary = handleBlockingAnnotations summary 
                  ~curstate:s.interruptState ~caller:(!curFunc).svar ~call in
  (* E.log "Calling %s, summary is %a\n" f.vname d_blockingState summary; *)
  match summary.precondition with
  | None -> s
  | Some (chain, wt) -> begin
      let chain' = call::chain, wt in

      match s.interruptState with
      | Top
      | Disabled ->
          (* This is an error!
             Report only one error per line *)
          begin
            let where = (!currentLoc, !curFunc, s.interruptState) in
            try
              let old = H.find blockingErrors where in
              H.replace blockingErrors where (shorter old chain')
            with Not_found ->
              (* First error on this line *)
              H.add blockingErrors where chain'
          end;
          s
      | Enabled | UnchangedEnabled ->
          s
      | IrqRestore -> 
          E.s (unimp 
                 "Calling a blocking function from an IRQ_RESTORE function")
      | Unchanged ->
          (*  since call has a precondition that interrupts be enabled,
              the current function now does as well. *)
          if s.precondition = None then
            raise (AddPrecondition chain')
          else
            (* The precondition already existed; choose the shorter reason. *)
            { s with precondition = betterMayBlock s.precondition (Some chain') }
    end

(* call this after callFunctionHandleMayBlock *)
let callFunctionSetNewIntState s call : blockingState =
  let (callee:varinfo),_,_,_ = call in
  let summary,_ = 
    try
      IH.find functionSummaries callee.vid
    with Not_found ->
      emptySummary,0
  in
  if summary.interruptState = Unchanged then
    s
  else if summary.interruptState =? s.interruptState then
    s
  else if summary.interruptState = UnchangedEnabled then
    assertInterruptsEnabled callee.vname s
  else if (hasAttribute "noblocking" callee.vattr) then
    s  (* We trust this function. *)
  else begin
    if summary.interruptState = Top then
      log "setting interrupt state = Top because of call to %s\n" callee.vname;
    {s with interruptState = summary.interruptState}
  end

(******* Flow functions **********)

(* State at each statement *)
let stateMap : blockingState IH.t = IH.create 50


let doInstr (i:instr) (old: blockingState) : blockingState =
  match i with
  | Asm(_,["sti" | "sti; hlt"],_,_,_,_) ->
      enableInterrupts old
  | Asm(_,["cli"],_,_,_,_) ->
      disableInterrupts old

  | Asm(_,["pushfl ; popl %0"],[None,_,lv],_,_,_) ->
      saveInterrupts old lv
  | Asm(_,["pushfl ; popl %0 ; cli"],[None,_,lv],_,_,_) ->
      let s = saveInterrupts old lv in
      disableInterrupts s
  | Asm(_,["pushl %0 ; popfl"],_,[None,_,Lval lv],_,_) ->
      restoreInterrupts old lv
  | Asm(_,["pushfl ; popl %0"|"pushfl ; popl %0 ; cli"|"pushl %0 ; popfl"],
        _,_,_,_) ->
      E.s (error "Bad arguments to assembly %a" d_instr i)

  | Asm(_,_,_,_,_,_) ->
(*       E.log "%a: Unknown assembly %a\n" d_loc !currentLoc d_instr i; *)
      old

      (* This call only returns if interrupts are enabled *)
  | Call(_,Lval(Var vf, NoOffset),_,_) when vf.vname = assertIntsEnabledFun ->
      assertInterruptsEnabled vf.vname old

  | Call(reto,Lval(Var vf, NoOffset),args,_) when 
      (hasAttribute "irq_restore" vf.vattr)
      || (hasAttribute "irq_save" vf.vattr) ->
      (* Maybe this function has an irq_save/irq_restore annotation on it.
         FIXME: if so, we consider only the annotation and ignore the summary*)
      if hasAttribute "irq_restore" vf.vattr then begin
        match filterAttributes "irq_restore" vf.vattr with
        | [Attr("irq_restore", [what])] ->
            if hasAttribute "irq_save" vf.vattr then
              E.s (unimp "irq_save and irq_restore on the same function");
            let what' = compileFunctionAttribute vf.vtype args ~reto what in
            restoreInterrupts old what'
        | _ -> E.s (error "bad irq_restore attribute on function")
      end
      else begin
        match filterAttributes "irq_save" vf.vattr with
        | [Attr("irq_save", [what])] ->
            let lv = compileFunctionAttribute vf.vtype args ~reto what in
            saveInterrupts old lv
        | _ -> E.s (error "bad irq_save attribute on function")
      end

  | Call(_,f,args,loc) ->
      (* For an indirect call, we may get many possible calls.
         Handle them in parallel: first, check the precondition summaries,
         then check the interruptState summaries. *)
      let calls = getCalls f args loc in
      let s' = 
        List.fold_left callFunctionHandleMayBlock
          old
          calls
      in
      let s'' = List.fold_left callFunctionSetNewIntState
                  s'
                  calls
      in
      s''

  | Set _ ->
      old

let joinInterruptBit olds news where: interruptBit =
  if olds =? news then olds
  else match olds, news with
(*         Unchanged, Enabled *)
(*       | Enabled, Unchanged -> *)
(*           if old.precondition <> None || newa.precondition <> None then *)
(*             E.s (bug "Has precondition = enabled, but has state = Unchanged."); *)
(*           (\* record this as a precondition and restart the function. *\) *)
(*           Dutil.warn "Blocking analysis: join of %a and %a means that %s has the precondition that interrupts are enabled." *)
(*             d_bit old.interruptState d_bit newa.interruptState *)
(*             (!curFunc).svar.vname; *)
(*           raise (AddPrecondition ([], JoinWithEnabled !currentLoc)) *)
  | Unchanged, UnchangedEnabled
  | UnchangedEnabled, Unchanged ->
      (* Along one path, we asserted that interrupts were enabled. *)
      Unchanged
  | Enabled, UnchangedEnabled
  | UnchangedEnabled, Enabled ->
      Enabled
  | Enabled, Unchanged
  | Unchanged, Enabled ->
      (* Hack to reduce the number of false positives.
         Assume that the join of Unchanged and Enabled is Unchanged.
         This is sound, since at most we will underestimate
         the locations at which interrupts are enabled.
         If we ever wanted to do e.g. a locking analysis, we'd have
         to remove this case *)
      Unchanged
  | _ -> begin
      if olds = Top || news = Top then
        (* Don't bother warning; we've already complained that the state 
           is Top *)
        ()
      else
        Dutil.warn 
          "inconsistent interrupt state%a: %a vs %a"
          insert where d_bit olds d_bit news;
      Top
    end

let joinStates ~old ~newa : blockingState option =
  if newa =? old then None
  else begin
    let interruptState = 
      joinInterruptBit old.interruptState newa.interruptState nil
    in
    let savedFlags =
      if newa.savedFlags =? old.savedFlags then 
        old.savedFlags
      else begin
        (* FIXME: reenable this notice *)
        (* Dutil.log "Blocking analysis: possible inconsistent saving of flags."; *)
        (* return the intersection of the lists *)
        List.fold_left
          (fun acc save ->
             if List.mem save old.savedFlags then save::acc else acc)
          []
          newa.savedFlags
      end
    in
    let precondition = (* if preconditionEnabled then Some [] else  *)
      (* It's okay for the precondition values to differ *)
      betterMayBlock old.precondition newa.precondition
    in
    (* if we were already at top and precondition hasn't changed, no need to keep
       exploring.  We've already warned about any problems. *)
    if (old.interruptState = interruptState) && old.precondition =? precondition then
      None
    else
      Some { interruptState = interruptState;
             precondition = precondition;
             savedFlags = savedFlags }
  end

let recordSummary (state: blockingState) : unit =
  (* Don't put IrqRestore in summaries *)
  let interruptSummary =
    if state.interruptState = IrqRestore then Unchanged
    else state.interruptState
  in
  match !curFuncSummary with
    None -> 
      curFuncSummary := Some { interruptState = interruptSummary;
                               precondition = state.precondition;
                               savedFlags = []};
  | Some oldSummary ->
      let interruptSummary =
        joinInterruptBit oldSummary.interruptState interruptSummary
          (text " at function return")
      in
      curFuncSummary := Some { interruptState = interruptSummary;
                               precondition = betterMayBlock 
                                            oldSummary.precondition 
                                            state.precondition;
                               savedFlags = []}


(* When an annotated function returns, ensure that it has done as the annotation
   promised.*)
let checkReturn (state: blockingState) ~(reto:exp option) : unit =
  if hasAttribute "irq_restore" (!curFunc).svar.vattr then begin
    if state.interruptState <> IrqRestore then
      E.s (error "irq_restore function does not restore the flags")
  end;
  begin
    match filterAttributes "irq_save" (!curFunc).svar.vattr with
      [] -> ()
    | [Attr("irq_save", [what])] ->
        (* Assert state includes what->Unchanged, indicating the initial value
           was saved in what. *)
        let ctx = Dattrs.formalsContext !curFunc in
        let ctx' = match reto with
            Some e -> Dattrs.addBinding ctx "__ret" e
          | None -> ctx
        in
        let what' = compileLvalAttribute ctx' what in
        if not (List.mem (what', Unchanged) state.savedFlags) then
          E.s (error "irq_save function does not save the flags correctly")
    | _ -> E.s (error "bad irq_save attribute on function")
  end

module InterruptsFlow = struct
  let name = "InterruptsEnabled"
  let debug = ref false
  type t = blockingState
  let copy x = x
  let stmtStartData : t IH.t = stateMap
  let pretty = d_blockingState
  let computeFirstPredecessor s a = a

  let combinePredecessors s ~(old:t) newa =
    if !debug then
      E.log "  Joining %a and %a at %d.\n"
        d_blockingState old d_blockingState newa s.sid;
    joinStates ~old ~newa

  let doInstr a i =
    DF.Done (doInstr a i)

  let doStmt s a =
    (* on Return, merge all of the states (interruptState and precondition only)
       into a summary *)
    (match s.skind with
       Return (reto,_) -> 
         checkReturn a ~reto;
         recordSummary a
     | _ -> ());
    DF.SDefault

  let doGuard e a =
    DF.GDefault

  let filterStmt s = true
end
module FlowEngine = DF.ForwardsDataFlow (InterruptsFlow)


let initialInterruptState (fd:fundec) oldSummary: blockingState =
  (* If this is an IRQ_RESTORE function, initialize the state to the
     exp that should be restored *)
  let savedFlags =
    match filterAttributes "irq_restore" fd.svar.vattr with
    | [] -> [] (* The common case *)
    | [Attr("irq_restore", [what])] ->
        if hasAttribute "irq_save" fd.svar.vattr then
          E.s (unimp "irq_save and irq_restore on the same function");
        let what' = compileLvalAttribute (Dattrs.formalsContext fd) what in
        (* When the function returns, we will check that the interrupt
           state has been set to this magic "IrqRestore" value that is only
           created here. *)
        [what',IrqRestore]
    | _ -> E.s (error "bad irq_restore attribute on function")
  in
  let interruptState =
    if oldSummary.precondition = None then Unchanged
    else Enabled
  in
  { interruptState = interruptState;
    precondition = oldSummary.precondition;
    savedFlags = savedFlags;
  }


let doBlockingAnalysis (f:file) : unit = 
  Stats.time "Cfg.computeFileCFG" Cfg.computeFileCFG f;

  let worklist : fundec list ref = ref [] in
  let addToWorklist (fn:fundec) : unit =
    if not (List.memq fn !worklist) then
      worklist := fn::!worklist
  in
  let inversecallgraph = buildInversecallgraph f in

  (* Returns true if the summary has changed. *)
  let rec doOneFunc (fd:fundec) : bool =
    let oldSummary, numPasses =
      try 
        let state, numPrevPasses = IH.find functionSummaries fd.svar.vid in
        state, numPrevPasses+1
      with Not_found ->
        (* If a function is not in the table, we use "emptySummary" as its
           summary. So compare the analysis results to emptySummary.
           If they are equivalent, we don't need to reanalyze functions that
           call this one. *)
        emptySummary, 1
    in
    E.log "Starting %s.  Pass %d\n" fd.svar.vname numPasses;
    try begin
      IH.clear stateMap;
      curFunc := fd;
      curFuncSummary := None;
      if (isLeaf fd.svar) && (numPasses >= 2) then
        E.s (bug "recomputing the summary for a leaf function.");
      let fst = List.hd fd.sbody.bstmts in
      IH.add stateMap fst.sid (initialInterruptState fd oldSummary);
      (* InterruptsFlow.debug := (fd.svar.vname = "ide_spin_wait_hwgroup"); *)
      Stats.time "DF.ForwardsDataFlow" FlowEngine.compute [fst];
      IH.clear stateMap;
      let cfs = !curFuncSummary in
      curFunc := dummyFunDec;
      curFuncSummary := None;

      (* Now look at the new summary *)
      match cfs with
      | None ->
          if not (hasAttribute "noreturn" fd.svar.vattr) then
            warn "Function has no reachable return statement.  Should it be labeled noreturn?";
          false
      | Some newSummary ->
          E.log " Done with %s.   Summary: %a\n"
            fd.svar.vname d_blockingState newSummary;

          (* Save the new summary.  Even if there is no official change,
             there may be a shorter precondition error. *)
          IH.replace functionSummaries fd.svar.vid (newSummary,numPasses);
          (* Has the summary changed? *)
          let oldmayblock = oldSummary.precondition <> None in
          let newmayblock = newSummary.precondition <> None in
          (* It's possible that we may change from a summary that blocks
             to one that doesn't, because of the discovery that it calls
             a function that enables interrupts before calling the blocking
             function. *)
(*               if oldmayblock && not newmayblock then *)
(*                 E.s (bug "analysis is broken"); *)
          (oldSummary.interruptState <> newSummary.interruptState)
          || (oldmayblock <> newmayblock)
    end
    with 
    | Failure "hd" ->
        false
    | AddPrecondition pre ->
        (* Add a precondition to a function summary that doesn't already 
           have one. *)
        if oldSummary.precondition <> None then
          E.s (bug "loop in AddPrecondition.");
        let newSummary = {emptySummary with precondition = Some pre} in
        IH.replace functionSummaries fd.svar.vid (newSummary,numPasses);
        (* Start over with the new precondition. *)
        ignore (doOneFunc fd);
        true (* This summary has changed even if the second call to doOneFunc
                has no changes. *)
  in
  
  (* Step 1: add everything to the worklist *)
  let leafFunctions: fundec list ref = ref [] in
  iterGlobals f
    (function GFun(fn, _) -> 
       if isLeaf fn.svar then
         leafFunctions := fn::!leafFunctions
       else
         addToWorklist fn 
       | _ -> () );
  (* Put leaf functions first in the worklist so we can
     make fewer passes over non-leaf functions. 
     Also, reverse the worklist in the hopes that callers are usually placed
     after callees.
     Note: this isn't really needed now that we have the defer list below,
     but it can't hurt.
  *)
  worklist := Util.list_append !leafFunctions (List.rev !worklist);
  if (!worklist = []) then
    E.s (error "No functions to do the blocking analysis on.");

  (* Step 2: iterate *)

  (* At first, we only analyze a function if everything it calls
     (except itself) has already been analyzed. *)
  let shouldDefer fd : bool = 
    let dependencies = callgraphLookup fd.svar in
    not (List.for_all 
           (fun (vf,_,_,_) -> vf == fd.svar || IH.mem functionSummaries vf.vid)
           dependencies)
  in
  let defer: fundec list ref = ref [] in
  let doWorklist (okayToDefer:bool) : unit = 
    while !worklist <> [] do
      let fd = List.hd !worklist in
      worklist := List.tl !worklist;
      if okayToDefer && (shouldDefer fd) then
        defer := fd::!defer
      else begin
        let changed = Stats.time "Blocking.doOneFunc" doOneFunc fd in
        if changed then begin
          let callers = 
            try IH.find inversecallgraph fd.svar.vid
            with Not_found -> []
          in
          List.iter addToWorklist callers
        end;
      end
    done
  in

  (* Start with non-recursive and simply-recursive functions. 
     (doWorklist true) will empty the worklist, but it may move some functions
     to defer.  Keep moving functions from defer back to the worklist.*)
  let rec loop (oldNumDeferred:int) =
    E.log "Beginning a pass over the worklist. %d funcs in worklist.\n"
          (List.length !worklist);
    assert (!defer = [] && !worklist <> []);
    doWorklist true;
    assert (!worklist = []);

    (* Now take things in the deferred list, and move them back to th
       worklist *)
    let numDeferred = List.length !defer in 
    if numDeferred > oldNumDeferred then
      E.s (bug "infinite loop.");
    worklist := List.rev !defer;
    defer := [];
    
    if numDeferred = 0 then
      () (* all done *)
    else if numDeferred = oldNumDeferred then begin
      E.log "The iteration algorithm is stuck; now processing all functions\n";
      (* We're stuck.  There must be mutually recursive functions in 
         the graph *)
      doWorklist false  (* No more procrastinating ... do every function now *)
    end
    else begin
      (* We're making progress, but we're not there yet. Keep going. *)
      loop numDeferred
    end
  in
  loop max_int;

  (* Step 3: report errors *)
  let reportOneError (loc,fd,st) (reason:mustEnable) : unit = 
    currentLoc := loc;
    let callChain, wt = reason in
    Dutil.error "Blocking error: when the interrupt state is %a, %s calls a function that requires them to be enabled.  Call trace:\n   %a\n    %a"
      d_bit st
      fd.svar.vname
      (docList ~sep:(text "\n   ") (d_call ())) callChain
      d_whyType wt
    ;
    ()
  in
  H.iter reportOneError blockingErrors;
  E.log "\nDone with the blocking analysis\n";
  flush !E.logChannel;

  Cfg.clearFileCFG f;
  ()



(****************************************************************************
 **  Part omega:  Cleanup and entrypoint                                   **
 ****************************************************************************)

let cleanup (): unit =
  IH.clear callgraph;
  IH.clear funcsOfNode;
  IH.clear functionSummaries;
  H.clear blockingErrors;
  IH.clear stateMap;
  ()



let blockingAnalysis (f:file) : unit =
  Stats.time "Compute the call graph" buildCallGraph f;
(*   Stats.time "Gc.full_major" Gc.full_major (); *)
(*   Gc.print_stat !E.logChannel; *)
(*   Ptrnode.initialize (); (\* Clear the state to free memory. *\) *)
(*   Stats.time "Gc.full_major" Gc.full_major (); *)
(*   Gc.print_stat !E.logChannel; *)
(*   flush !E.logChannel; *)
  Stats.time "Infer blocking functions" doBlockingAnalysis f;
  cleanup ();
  ()

