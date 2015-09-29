(*
 * sfunctions.ml
 *
 * These are utility functions for instrumenting a program for SharC's
 * dynamic analysis.
 *
 *)

open Cil

type functions = {
    mutable init_system:varinfo;
    mutable init_thread:varinfo;

    mutable add_lock:varinfo;
    mutable rm_lock:varinfo;
    mutable chk_lock:varinfo;
    mutable coerce_lock:varinfo;

    mutable dynbar:varinfo;
    mutable dynbar_read:varinfo;
    mutable dynbar_write:varinfo;
    mutable coerce_dynbar:varinfo;
    mutable readdynbarrange:varinfo;
    mutable writedynbarrange:varinfo;

    mutable read:varinfo;
    mutable write:varinfo;
    mutable readrange:varinfo;
    mutable writerange:varinfo;

    mutable fakecast:varinfo;    (* SCAST's get changed to sharingcast's *)
    mutable sharingcast:varinfo;

    mutable sinit:varinfo;
    mutable chk_single_threaded:varinfo;

    mutable strlen:varinfo;
}

let dummyVar = makeVarinfo false "foo" voidType

let sfuncs = {
    init_system = dummyVar;
    init_thread = dummyVar;

    add_lock = dummyVar;
    rm_lock = dummyVar;
    chk_lock = dummyVar;
    coerce_lock = dummyVar;

    dynbar = dummyVar;
    dynbar_read = dummyVar;
    dynbar_write = dummyVar;
    coerce_dynbar = dummyVar;
    readdynbarrange = dummyVar;
    writedynbarrange = dummyVar;

    read = dummyVar;
    write = dummyVar;
    readrange = dummyVar;
    writerange = dummyVar;

    fakecast = dummyVar;
    sharingcast = dummyVar;

    sinit = dummyVar;
    chk_single_threaded = dummyVar;

    strlen = dummyVar;
}

let sharc_function_names =
    ["__sharc_init_system";"__sharc_thread_init";
     "__sharc_add_lock";"__sharc_rm_lock";
     "__sharc_chk_lock";"__sharc_coerce_lock";
     "__sharc_dynbar";"__sharc_dybar_read";
     "__sharc_dynbar_write";"__sharc_coerce_dynbar";
     "__sharc_dynbar_readrange";"__sharc_dynbar_writerange";
     "__sharc_read"; "__sharc_write";
     "__sharc_read_range"; "__sharc_write_range";
     "SCAST"; "__sharc_sharing_cast";
     "SINIT"; "__sharc_single_threaded";
     "__sharc_strlen";]

let initSharCFunctions (f : file) : unit =
    let ufuntype = TFun(voidType, Some [], false, []) in

    let vfuntype = TFun(voidType, Some["x",voidPtrType,[]],false,[]) in
    let vrvfunctype = TFun(voidPtrType, Some["addr",voidPtrType,[]],false,[]) in

    let vpvpuicpargs = ["lck",voidPtrType,[]; "what", voidPtrType,[];
                        "sz", uintType, []; "msg", charPtrType, []]
    in
    let vvsmtype = TFun(voidType,Some vpvpuicpargs,false,[]) in

    let vvmtype = TFun(voidType,Some["dstl",voidPtrType,[];
                                     "srcl",voidPtrType,[];
                                     "msg",charPtrType,[]],false,[]) in

    let vpcpargs = ["x", voidPtrType, []; "msg", charPtrType, []] in
    let accfntype = TFun(voidType, Some vpcpargs, false, []) in

    let shcastargs = ["addr",voidPtrType,[];"slog",TPtr(voidPtrType,[]),[];
                      "slotlocal",uintType,[];
                      "lo",ulongType,[];"hi",ulongType,[];"msg",charPtrType,[]]
    in
    let shcastfntype = TFun(voidPtrType,Some shcastargs,false,[]) in

    let rangeargs = ["addr",voidPtrType,[];"sz",uintType,[];
                     "msg",charPtrType,[]]
    in
    let rangechktype = TFun(voidType, Some rangeargs, false, []) in

    let dynbarrangeargs = ["bar",voidPtrType,[];"addr",voidPtrType,[];"sz",uintType,[];
                     "msg",charPtrType,[]]
    in
    let dynbarrangechktype = TFun(voidType, Some dynbarrangeargs, false, []) in

    let strlentype = TFun(uintType,Some["str",charPtrType,[]],false,[]) in

    sfuncs.init_system <- findOrCreateFunc f "__sharc_init_system" ufuntype;
    sfuncs.init_thread <- findOrCreateFunc f "__sharc_thread_init" ufuntype;

    sfuncs.add_lock <- findOrCreateFunc f "__sharc_add_lock" vfuntype;
    sfuncs.rm_lock <- findOrCreateFunc f "__sharc_rm_lock" vfuntype;
    sfuncs.chk_lock <- findOrCreateFunc f "__sharc_chk_lock" vvsmtype;
    sfuncs.coerce_lock <- findOrCreateFunc f "__sharc_coerce_lock" vvmtype;

    sfuncs.dynbar <- findOrCreateFunc f "__sharc_dynbar" vfuntype;
    sfuncs.dynbar_read <- findOrCreateFunc f "__sharc_dynbar_read" vvmtype;
    sfuncs.dynbar_write <- findOrCreateFunc f "__sharc_dynbar_write" vvmtype;
    sfuncs.coerce_dynbar <- findOrCreateFunc f "__sharc_coerce_dynbar" vvmtype;
    sfuncs.readdynbarrange <- findOrCreateFunc f "__sharc_dynbar_readrange" dynbarrangechktype;
    sfuncs.writedynbarrange <- findOrCreateFunc f "__sharc_dynbar_writerange" dynbarrangechktype;

    sfuncs.read <- findOrCreateFunc f "__sharc_read" accfntype;
    sfuncs.write <- findOrCreateFunc f "__sharc_write" accfntype;
    sfuncs.readrange <- findOrCreateFunc f "__sharc_read_range" rangechktype;
    sfuncs.writerange <- findOrCreateFunc f "__sharc_write_range" rangechktype;

    sfuncs.fakecast <- findOrCreateFunc f "SCAST" vrvfunctype;
    sfuncs.sharingcast <- findOrCreateFunc f "__sharc_sharing_cast" shcastfntype;

    sfuncs.sinit <- findOrCreateFunc f "SINIT" vrvfunctype;
    sfuncs.chk_single_threaded <- findOrCreateFunc f "__sharc_single_threaded"
        vfuntype;

    sfuncs.strlen <- findOrCreateFunc f "__sharc_strlen" strlentype;
