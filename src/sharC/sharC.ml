open Cil
open Ivyutil
open Sutil

let preprocess (f : file) : unit = ()

let post_deputy (f : file) : unit =
    if !Ivyoptions.noSharC then () else begin
        let woc = !Ivyoptions.globalAnalysis = "" in

        Sfunctions.initSharCFunctions f;
        Ssharinganalysis.localSharingAnalysis ~warnOnChange:woc f.globals;
        Stypefixer.fixTypes f
    end


let pthread_fn_type = TPtr(TFun(voidPtrType,Some["arg",voidPtrType,[]],false,[]),[])
let pthread_arg_type = voidPtrType
class pthreadCallFixerClass = object(self)
    inherit nopCilVisitor

    method vinst (i : instr) =
        match i with
        | Call(ro,Lval(Var fv,NoOffset),[tid;attr;fn;arg],loc)
          when fv.vname = "pthread_create" ->
            ChangeTo[Call(ro,Lval(Var fv,NoOffset),
                     [tid;attr;CastE(pthread_fn_type,fn);
                               CastE(pthread_arg_type,arg)],loc)]
        | _ -> SkipChildren

end


(* XXX: cast arguments to pthread_create to the right types *)
let postProcessFile (f : file) =
  (* Add #include directive for opsFile *)
  f.globals <- (GText ("#include <" ^ !Ivyoptions.sharcOpsFile ^ ">\n\n"))::f.globals;
  ()

let process (f : file) : file =
    if !Ivyoptions.noSharC then begin
        Sutil.dropSharCAttrs f Sutil.sharc_attrs;
        f
    end else begin
        ignore(Stypechecker.checkSharingTypes f);

        Sdynamic.processFile f;
        Soptim.registerIgnoreInst Dcheckdef.isDeputyFunctionInstr;
        Soptim.registerIgnoreInst Rcutils.isRcInstr;
        Soptim.registerIgnoreInst isPthreadCall;
        Soptim.optimFile f;

        Sreadonly.readOnlyTypeCheck f;
        Slockcheck.instrumentLocks f;
        Slockcheck.checkSlockedTypes f;
        Sdynbar.instrumentBarriers f;
        Sdynbar.checkDynBarTypes f;

        visitCilFile (new pthreadCallFixerClass) f;

        printFile ~extraPrinting:None ~globinit:None
                  ~printer:(sharcPrinter :> cilPrinter)
                  f (f.fileName^".sh.i");

        Sutil.dropSharCAttrs f Sutil.sharc_attrs;
        postProcessFile f;
        f
    end
