(*
 * sreadonly.ml
 *
 * Static checking for the readonly type.
 *
 *)

open Cil
open Pretty
open Ivyoptions
open Sutil
open Sfunctions

module E = Errormsg

(* SREADONLY fields of SPRIVATE structs may be written *)
let isWritableReadonlyLval (lv : lval) : bool =
    let hlv, lastoff = removeOffsetLval lv in
    match lastoff with
    | Field(fi,NoOffset)
      when isPrivateType (sharCTypeOfLval hlv) -> true
    | _ ->
        E.log "not writable readonly lval %a of %a:%a\n"
            sp_lval lv sp_lval hlv sp_type (sharCTypeOfLval hlv);
        false

let chk_single_threaded loc =
    let lmsg = sprint ~width:80 (d_loc () loc) in
    let msg = mkString lmsg in
    Call(None,v2e sfuncs.chk_single_threaded,[msg],loc)

class readOnlyTypeCheckerClass (checks : bool ref) = object(self)
    inherit nopCilVisitor

    method vinst (i : instr) =
        match i with
        | Set(lv, _, loc)
          when isReadonlyType (sharCTypeOfLval lv) &&
               not(isWritableReadonlyLval lv) ->
            E.error "Write to readonly lval %a at %a in %a"
                sp_lval lv d_loc loc sp_instr i;
            checks := false;
            SkipChildren
        | Call(Some lv,Lval(Var fv,NoOffset),[src],loc)
          when isReadonlyType(sharCTypeOfLval lv) &&
               fv.vname = "SINIT" || fv.vname = "SINIT_DOUBLE" ||
               fv.vname = "SINIT_FLOAT" ->
            (* SREADONLYs can be initialized when there is only
               one thread running *)
            ChangeTo[chk_single_threaded loc;
                     Set(lv, src, loc)]
        | Call(Some lv, _, _, loc)
          when isReadonlyType(sharCTypeOfLval lv) &&
               not(isWritableReadonlyLval lv) ->
            E.error "Write to readonly lval %a at %a in %a"
                sp_lval lv d_loc loc sp_instr i;
            checks := false;
            SkipChildren
        | _ -> SkipChildren

    method vblock (b : block) =
        if hasAttribute "trusted" b.battrs
        then SkipChildren
        else DoChildren

end

let readOnlyTypeCheck (f : file) : unit =
    let checks = ref true in
    let vis = new readOnlyTypeCheckerClass checks in
    visitCilFile vis f
