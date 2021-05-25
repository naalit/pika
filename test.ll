; ModuleID = 'main'
source_filename = "src/runtime/prelude.ll"
target triple = "x86_64-pc-linux-gnu"

module asm ".globl __LLVM_StackMaps"

%struct_alloc = type { i8 addrspace(1)*, i8 addrspace(1)*, i8 addrspace(1)* }

@local_alloc = external thread_local global %struct_alloc, align 8
@istr = private unnamed_addr constant [4 x i8] c"%d\0A\00", align 1
@rtti_const_rtti = unnamed_addr constant i32 4, align 8
@rtti_const_rtti.1 = unnamed_addr constant i32 4, align 8
@rtti_const_rtti.2 = unnamed_addr constant i32 4, align 8
@rtti_const_rtti.3 = unnamed_addr constant i32 4, align 8
@stop_closure = global void (i8 addrspace(1)*, i8 addrspace(1)*)* null

declare void @initialize(i32)

declare void @finalize()

declare i8 addrspace(1)* @immix_alloc(i64, i32 addrspace(1)*, i8*)

; Function Attrs: cold noinline
define private i8 addrspace(1)* @gc_alloc_slow(i64 %size, i32 addrspace(1)* %header) #0 {
  %rsp = call i8* @llvm.addressofreturnaddress.p0i8()
  %alloc = call i8 addrspace(1)* @immix_alloc(i64 %size, i32 addrspace(1)* %header, i8* %rsp)
  ret i8 addrspace(1)* %alloc
}

; Function Attrs: noinline
define private fastcc i8 addrspace(1)* @get_base_pointer(i8 addrspace(1)* %0) #1 {
  %2 = getelementptr inbounds i8, i8 addrspace(1)* %0, i32 8
  ret i8 addrspace(1)* %2
}

define private fastcc i8 addrspace(1)* @gc_alloc(i64 %size1, i32 addrspace(1)* %header) gc "statepoint-example" {
  %size2 = add i64 %size1, 8
  %size3 = add i64 %size2, 7
  %size = and i64 %size3, -8
  %nsize = mul i64 %size, -1
  %heapPtr = getelementptr inbounds %struct_alloc, %struct_alloc* @local_alloc, i64 0, i32 2
  %heapEnd = getelementptr inbounds %struct_alloc, %struct_alloc* @local_alloc, i64 0, i32 1
  %ptr = load i8 addrspace(1)*, i8 addrspace(1)** %heapPtr, align 8
  %next = getelementptr inbounds i8, i8 addrspace(1)* %ptr, i64 %nsize
  %end = load i8 addrspace(1)*, i8 addrspace(1)** %heapEnd, align 8
  %cond = icmp slt i8 addrspace(1)* %next, %end
  br i1 %cond, label %slow, label %fast

slow:                                             ; preds = %0
  %r = call i8 addrspace(1)* @gc_alloc_slow(i64 %size, i32 addrspace(1)* %header)
  ret i8 addrspace(1)* %r

fast:                                             ; preds = %0
  store i8 addrspace(1)* %next, i8 addrspace(1)** %heapPtr, align 8
  %next.rtti = bitcast i8 addrspace(1)* %next to i32 addrspace(1)* addrspace(1)*
  store i32 addrspace(1)* %header, i32 addrspace(1)* addrspace(1)* %next.rtti, align 8
  %alloc = call fastcc i8 addrspace(1)* @get_base_pointer(i8 addrspace(1)* %next)
  ret i8 addrspace(1)* %alloc
}

declare i32 @printf(i8*, ...)

define {} @print_i32(i32 %a) {
  %_0 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([4 x i8], [4 x i8]* @istr, i32 0, i32 0), i32 %a)
  ret {} undef
}

; Function Attrs: nounwind readnone
declare i8* @llvm.addressofreturnaddress.p0i8() #2

define tailcc void @"fun$0"() gc "statepoint-example" {
entry:
  br label %"0$0"

"0$0":                                            ; preds = %entry
  ret void
}

define tailcc void @"u$fun$0"(i8 addrspace(1)* %env) gc "statepoint-example" {
entry:
  %env_slots = getelementptr inbounds i8, i8 addrspace(1)* %env, i32 8
  tail call tailcc void @"fun$0"()
  ret void
}

define tailcc void @"fun$16"() gc "statepoint-example" {
entry:
  br label %"16$16"

"16$16":                                          ; preds = %entry
  ret void
}

define tailcc void @"u$fun$16"(i8 addrspace(1)* %env) gc "statepoint-example" {
entry:
  %env_slots = getelementptr inbounds i8, i8 addrspace(1)* %env, i32 8
  tail call tailcc void @"fun$16"()
  ret void
}

define tailcc {} @"fun$70"(i32 %0) gc "statepoint-example" {
entry:
  %"72" = alloca i32, align 4
  %"76" = alloca {}, align 8
  store i32 %0, i32* %"72", align 4
  br label %"70$70"

"70$70":                                          ; preds = %entry
  %param = load i32, i32* %"72", align 4
  %extern_call = tail call {} @print_i32(i32 %param)
  store {} %extern_call, {}* %"76", align 1
  br label %"70$74"

"70$74":                                          ; preds = %"70$70"
  %param1 = load {}, {}* %"76", align 1
  ret {} %param1
}

define tailcc void @"u$fun$70"(i8 addrspace(1)* %0, i8 addrspace(1)* %1, i8 addrspace(1)* %env) gc "statepoint-example" {
entry:
  %env_slots = getelementptr inbounds i8, i8 addrspace(1)* %env, i32 8
  %from_any = ptrtoint i8 addrspace(1)* %0 to i64
  %int_unmarked = ashr i64 %from_any, 1
  %to_i = trunc i64 %int_unmarked to i32
  %casted_load_slot = bitcast i8 addrspace(1)* %1 to void (i8 addrspace(1)*, i8 addrspace(1)*)* addrspace(1)* addrspace(1)*
  %load = load void (i8 addrspace(1)*, i8 addrspace(1)*)* addrspace(1)*, void (i8 addrspace(1)*, i8 addrspace(1)*)* addrspace(1)* addrspace(1)* %casted_load_slot, align 8
  %stack_call = tail call tailcc {} @"fun$70"(i32 %to_i)
  %fun_ptr = load void (i8 addrspace(1)*, i8 addrspace(1)*)*, void (i8 addrspace(1)*, i8 addrspace(1)*)* addrspace(1)* %load, align 8
  %closure_env = bitcast void (i8 addrspace(1)*, i8 addrspace(1)*)* addrspace(1)* %load to i8 addrspace(1)*
  %rtti_slot = call fastcc i8 addrspace(1)* @gc_alloc(i64 4, i32 addrspace(1)* addrspacecast (i32* @rtti_const_rtti to i32 addrspace(1)*))
  %rtti_slot_i32 = bitcast i8 addrspace(1)* %rtti_slot to i32 addrspace(1)*
  store i32 0, i32 addrspace(1)* %rtti_slot_i32, align 4
  %rtti_slots = getelementptr inbounds i32, i32 addrspace(1)* %rtti_slot_i32, i32 1
  %rtti_slot_i321 = bitcast i8 addrspace(1)* %rtti_slot to i32 addrspace(1)*
  %any_slot = call fastcc i8 addrspace(1)* @gc_alloc(i64 0, i32 addrspace(1)* %rtti_slot_i321)
  tail call tailcc void %fun_ptr(i8 addrspace(1)* %any_slot, i8 addrspace(1)* %closure_env)
  ret void
}

define tailcc float @e(float %0) gc "statepoint-example" {
entry:
  %x = alloca float, align 4
  store float %0, float* %x, align 4
  br label %"e$e"

"e$e":                                            ; preds = %entry
  %param = load float, float* %x, align 4
  %binop = fmul float %param, 2.000000e+00
  %binop1 = fadd float 0x405FFAE140000000, %binop
  ret float %binop1
}

define tailcc void @"u$e"(i8 addrspace(1)* %0, i8 addrspace(1)* %1, i8 addrspace(1)* %env) gc "statepoint-example" {
entry:
  %env_slots = getelementptr inbounds i8, i8 addrspace(1)* %env, i32 8
  %from_any = ptrtoint i8 addrspace(1)* %0 to i64
  %int_unmarked = ashr i64 %from_any, 1
  %to_i = trunc i64 %int_unmarked to i32
  %to_f32 = bitcast i32 %to_i to float
  %casted_load_slot = bitcast i8 addrspace(1)* %1 to void (i8 addrspace(1)*, i8 addrspace(1)*)* addrspace(1)* addrspace(1)*
  %load = load void (i8 addrspace(1)*, i8 addrspace(1)*)* addrspace(1)*, void (i8 addrspace(1)*, i8 addrspace(1)*)* addrspace(1)* addrspace(1)* %casted_load_slot, align 8
  %stack_call = tail call tailcc float @e(float %to_f32)
  %fun_ptr = load void (i8 addrspace(1)*, i8 addrspace(1)*)*, void (i8 addrspace(1)*, i8 addrspace(1)*)* addrspace(1)* %load, align 8
  %closure_env = bitcast void (i8 addrspace(1)*, i8 addrspace(1)*)* addrspace(1)* %load to i8 addrspace(1)*
  %to_i32 = bitcast float %stack_call to i32
  %to_i64 = zext i32 %to_i32 to i64
  %int_shl = shl i64 %to_i64, 1
  %int_mark = or i64 %int_shl, 1
  %inttoptr = call i8 addrspace(1)* @"$_i2p"(i64 %int_mark)
  tail call tailcc void %fun_ptr(i8 addrspace(1)* %inttoptr, i8 addrspace(1)* %closure_env)
  ret void
}

define tailcc void @"fun$4"() gc "statepoint-example" {
entry:
  br label %"4$4"

"4$4":                                            ; preds = %entry
  ret void
}

define tailcc void @"u$fun$4"(i8 addrspace(1)* %env) gc "statepoint-example" {
entry:
  %env_slots = getelementptr inbounds i8, i8 addrspace(1)* %env, i32 8
  tail call tailcc void @"fun$4"()
  ret void
}

define tailcc void @"fun$12"() gc "statepoint-example" {
entry:
  br label %"12$12"

"12$12":                                          ; preds = %entry
  ret void
}

define tailcc void @"u$fun$12"(i8 addrspace(1)* %env) gc "statepoint-example" {
entry:
  %env_slots = getelementptr inbounds i8, i8 addrspace(1)* %env, i32 8
  tail call tailcc void @"fun$12"()
  ret void
}

define tailcc void @"fun$28"() gc "statepoint-example" {
entry:
  br label %"28$28"

"28$28":                                          ; preds = %entry
  ret void
}

define tailcc void @"u$fun$28"(i8 addrspace(1)* %env) gc "statepoint-example" {
entry:
  %env_slots = getelementptr inbounds i8, i8 addrspace(1)* %env, i32 8
  tail call tailcc void @"fun$28"()
  ret void
}

define tailcc void @"pk$main"({} %0, void (i8 addrspace(1)*, i8 addrspace(1)*)* addrspace(1)* %1) gc "statepoint-example" {
entry:
  %2 = alloca {}, align 8
  %"$cont.return.%30" = alloca void (i8 addrspace(1)*, i8 addrspace(1)*)* addrspace(1)*, align 8
  %3 = alloca {}, align 8
  %4 = alloca {}, align 8
  %"80" = alloca {}, align 8
  store {} %0, {}* %2, align 1
  store void (i8 addrspace(1)*, i8 addrspace(1)*)* addrspace(1)* %1, void (i8 addrspace(1)*, i8 addrspace(1)*)* addrspace(1)** %"$cont.return.%30", align 8
  br label %"main$main"

"main$main":                                      ; preds = %entry
  %stack_call = tail call tailcc {} @"fun$40"(i32 930)
  store {} %stack_call, {}* %3, align 1
  br label %"main$49"

"main$49":                                        ; preds = %"main$main"
  %stack_call1 = tail call tailcc {} @"fun$55"(i32 12)
  store {} %stack_call1, {}* %4, align 1
  br label %"main$64"

"main$64":                                        ; preds = %"main$49"
  %stack_call2 = tail call tailcc {} @"fun$70"(i32 5)
  store {} %stack_call2, {}* %"80", align 1
  br label %"main$79"

"main$79":                                        ; preds = %"main$64"
  %param = load {}, {}* %"80", align 1
  %param3 = load void (i8 addrspace(1)*, i8 addrspace(1)*)* addrspace(1)*, void (i8 addrspace(1)*, i8 addrspace(1)*)* addrspace(1)** %"$cont.return.%30", align 8
  %fun_ptr = load void (i8 addrspace(1)*, i8 addrspace(1)*)*, void (i8 addrspace(1)*, i8 addrspace(1)*)* addrspace(1)* %param3, align 8
  %closure_env = bitcast void (i8 addrspace(1)*, i8 addrspace(1)*)* addrspace(1)* %param3 to i8 addrspace(1)*
  %rtti_slot = call fastcc i8 addrspace(1)* @gc_alloc(i64 4, i32 addrspace(1)* addrspacecast (i32* @rtti_const_rtti.3 to i32 addrspace(1)*))
  %rtti_slot_i32 = bitcast i8 addrspace(1)* %rtti_slot to i32 addrspace(1)*
  store i32 0, i32 addrspace(1)* %rtti_slot_i32, align 4
  %rtti_slots = getelementptr inbounds i32, i32 addrspace(1)* %rtti_slot_i32, i32 1
  %rtti_slot_i324 = bitcast i8 addrspace(1)* %rtti_slot to i32 addrspace(1)*
  %any_slot = call fastcc i8 addrspace(1)* @gc_alloc(i64 0, i32 addrspace(1)* %rtti_slot_i324)
  tail call tailcc void %fun_ptr(i8 addrspace(1)* %any_slot, i8 addrspace(1)* %closure_env)
  ret void
}

define tailcc void @"u$main"(i8 addrspace(1)* %0, i8 addrspace(1)* %1, i8 addrspace(1)* %env) gc "statepoint-example" {
entry:
  %env_slots = getelementptr inbounds i8, i8 addrspace(1)* %env, i32 8
  %casted_load_slot = bitcast i8 addrspace(1)* %1 to void (i8 addrspace(1)*, i8 addrspace(1)*)* addrspace(1)* addrspace(1)*
  %load = load void (i8 addrspace(1)*, i8 addrspace(1)*)* addrspace(1)*, void (i8 addrspace(1)*, i8 addrspace(1)*)* addrspace(1)* addrspace(1)* %casted_load_slot, align 8
  tail call tailcc void @"pk$main"({} undef, void (i8 addrspace(1)*, i8 addrspace(1)*)* addrspace(1)* %load)
  ret void
}

define tailcc {} @"fun$40"(i32 %0) gc "statepoint-example" {
entry:
  %"42" = alloca i32, align 4
  %"46" = alloca {}, align 8
  store i32 %0, i32* %"42", align 4
  br label %"40$40"

"40$40":                                          ; preds = %entry
  %param = load i32, i32* %"42", align 4
  %extern_call = tail call {} @print_i32(i32 %param)
  store {} %extern_call, {}* %"46", align 1
  br label %"40$44"

"40$44":                                          ; preds = %"40$40"
  %param1 = load {}, {}* %"46", align 1
  ret {} %param1
}

define tailcc void @"u$fun$40"(i8 addrspace(1)* %0, i8 addrspace(1)* %1, i8 addrspace(1)* %env) gc "statepoint-example" {
entry:
  %env_slots = getelementptr inbounds i8, i8 addrspace(1)* %env, i32 8
  %from_any = ptrtoint i8 addrspace(1)* %0 to i64
  %int_unmarked = ashr i64 %from_any, 1
  %to_i = trunc i64 %int_unmarked to i32
  %casted_load_slot = bitcast i8 addrspace(1)* %1 to void (i8 addrspace(1)*, i8 addrspace(1)*)* addrspace(1)* addrspace(1)*
  %load = load void (i8 addrspace(1)*, i8 addrspace(1)*)* addrspace(1)*, void (i8 addrspace(1)*, i8 addrspace(1)*)* addrspace(1)* addrspace(1)* %casted_load_slot, align 8
  %stack_call = tail call tailcc {} @"fun$40"(i32 %to_i)
  %fun_ptr = load void (i8 addrspace(1)*, i8 addrspace(1)*)*, void (i8 addrspace(1)*, i8 addrspace(1)*)* addrspace(1)* %load, align 8
  %closure_env = bitcast void (i8 addrspace(1)*, i8 addrspace(1)*)* addrspace(1)* %load to i8 addrspace(1)*
  %rtti_slot = call fastcc i8 addrspace(1)* @gc_alloc(i64 4, i32 addrspace(1)* addrspacecast (i32* @rtti_const_rtti.1 to i32 addrspace(1)*))
  %rtti_slot_i32 = bitcast i8 addrspace(1)* %rtti_slot to i32 addrspace(1)*
  store i32 0, i32 addrspace(1)* %rtti_slot_i32, align 4
  %rtti_slots = getelementptr inbounds i32, i32 addrspace(1)* %rtti_slot_i32, i32 1
  %rtti_slot_i321 = bitcast i8 addrspace(1)* %rtti_slot to i32 addrspace(1)*
  %any_slot = call fastcc i8 addrspace(1)* @gc_alloc(i64 0, i32 addrspace(1)* %rtti_slot_i321)
  tail call tailcc void %fun_ptr(i8 addrspace(1)* %any_slot, i8 addrspace(1)* %closure_env)
  ret void
}

define tailcc void @"fun$8"() gc "statepoint-example" {
entry:
  br label %"8$8"

"8$8":                                            ; preds = %entry
  ret void
}

define tailcc void @"u$fun$8"(i8 addrspace(1)* %env) gc "statepoint-example" {
entry:
  %env_slots = getelementptr inbounds i8, i8 addrspace(1)* %env, i32 8
  tail call tailcc void @"fun$8"()
  ret void
}

define tailcc {} @"fun$55"(i32 %0) gc "statepoint-example" {
entry:
  %"57" = alloca i32, align 4
  %"61" = alloca {}, align 8
  store i32 %0, i32* %"57", align 4
  br label %"55$55"

"55$55":                                          ; preds = %entry
  %param = load i32, i32* %"57", align 4
  %extern_call = tail call {} @print_i32(i32 %param)
  store {} %extern_call, {}* %"61", align 1
  br label %"55$59"

"55$59":                                          ; preds = %"55$55"
  %param1 = load {}, {}* %"61", align 1
  ret {} %param1
}

define tailcc void @"u$fun$55"(i8 addrspace(1)* %0, i8 addrspace(1)* %1, i8 addrspace(1)* %env) gc "statepoint-example" {
entry:
  %env_slots = getelementptr inbounds i8, i8 addrspace(1)* %env, i32 8
  %from_any = ptrtoint i8 addrspace(1)* %0 to i64
  %int_unmarked = ashr i64 %from_any, 1
  %to_i = trunc i64 %int_unmarked to i32
  %casted_load_slot = bitcast i8 addrspace(1)* %1 to void (i8 addrspace(1)*, i8 addrspace(1)*)* addrspace(1)* addrspace(1)*
  %load = load void (i8 addrspace(1)*, i8 addrspace(1)*)* addrspace(1)*, void (i8 addrspace(1)*, i8 addrspace(1)*)* addrspace(1)* addrspace(1)* %casted_load_slot, align 8
  %stack_call = tail call tailcc {} @"fun$55"(i32 %to_i)
  %fun_ptr = load void (i8 addrspace(1)*, i8 addrspace(1)*)*, void (i8 addrspace(1)*, i8 addrspace(1)*)* addrspace(1)* %load, align 8
  %closure_env = bitcast void (i8 addrspace(1)*, i8 addrspace(1)*)* addrspace(1)* %load to i8 addrspace(1)*
  %rtti_slot = call fastcc i8 addrspace(1)* @gc_alloc(i64 4, i32 addrspace(1)* addrspacecast (i32* @rtti_const_rtti.2 to i32 addrspace(1)*))
  %rtti_slot_i32 = bitcast i8 addrspace(1)* %rtti_slot to i32 addrspace(1)*
  store i32 0, i32 addrspace(1)* %rtti_slot_i32, align 4
  %rtti_slots = getelementptr inbounds i32, i32 addrspace(1)* %rtti_slot_i32, i32 1
  %rtti_slot_i321 = bitcast i8 addrspace(1)* %rtti_slot to i32 addrspace(1)*
  %any_slot = call fastcc i8 addrspace(1)* @gc_alloc(i64 0, i32 addrspace(1)* %rtti_slot_i321)
  tail call tailcc void %fun_ptr(i8 addrspace(1)* %any_slot, i8 addrspace(1)* %closure_env)
  ret void
}

; Function Attrs: noinline
define private i8 addrspace(1)* @"$_i2p"(i64 %0) #1 {
entry:
  %inttoptr = inttoptr i64 %0 to i8 addrspace(1)*
  ret i8 addrspace(1)* %inttoptr
}

define i32 @main() gc "statepoint-example" {
entry:
  call void @initialize(i32 8)
  store void (i8 addrspace(1)*, i8 addrspace(1)*)* @"$_stop", void (i8 addrspace(1)*, i8 addrspace(1)*)** @stop_closure, align 8
  call tailcc void @"pk$main"({} undef, void (i8 addrspace(1)*, i8 addrspace(1)*)* addrspace(1)* addrspacecast (void (i8 addrspace(1)*, i8 addrspace(1)*)** @stop_closure to void (i8 addrspace(1)*, i8 addrspace(1)*)* addrspace(1)*))
  ret i32 0
}

define tailcc void @"$_stop"(i8 addrspace(1)* %0, i8 addrspace(1)* %1) {
entry:
  ret void
}

attributes #0 = { cold noinline }
attributes #1 = { noinline }
attributes #2 = { nounwind readnone }
