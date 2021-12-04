
// ** Expanded prelude

// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

// Basic theory for vectors using arrays. This version of vectors is not extensional.

type {:datatype} Vec _;

function {:constructor} Vec<T>(v: [int]T, l: int): Vec T;

function {:builtin "MapConst"} MapConstVec<T>(T): [int]T;
function DefaultVecElem<T>(): T;
function {:inline} DefaultVecMap<T>(): [int]T { MapConstVec(DefaultVecElem()) }

function {:inline} EmptyVec<T>(): Vec T {
    Vec(DefaultVecMap(), 0)
}

function {:inline} MakeVec1<T>(v: T): Vec T {
    Vec(DefaultVecMap()[0 := v], 1)
}

function {:inline} MakeVec2<T>(v1: T, v2: T): Vec T {
    Vec(DefaultVecMap()[0 := v1][1 := v2], 2)
}

function {:inline} MakeVec3<T>(v1: T, v2: T, v3: T): Vec T {
    Vec(DefaultVecMap()[0 := v1][1 := v2][2 := v3], 3)
}

function {:inline} MakeVec4<T>(v1: T, v2: T, v3: T, v4: T): Vec T {
    Vec(DefaultVecMap()[0 := v1][1 := v2][2 := v3][3 := v4], 4)
}

function {:inline} ExtendVec<T>(v: Vec T, elem: T): Vec T {
    (var l := l#Vec(v);
    Vec(v#Vec(v)[l := elem], l + 1))
}

function {:inline} ReadVec<T>(v: Vec T, i: int): T {
    v#Vec(v)[i]
}

function {:inline} LenVec<T>(v: Vec T): int {
    l#Vec(v)
}

function {:inline} IsEmptyVec<T>(v: Vec T): bool {
    l#Vec(v) == 0
}

function {:inline} RemoveVec<T>(v: Vec T): Vec T {
    (var l := l#Vec(v) - 1;
    Vec(v#Vec(v)[l := DefaultVecElem()], l))
}

function {:inline} RemoveAtVec<T>(v: Vec T, i: int): Vec T {
    (var l := l#Vec(v) - 1;
    Vec(
        (lambda j: int ::
           if j >= 0 && j < l then
               if j < i then v#Vec(v)[j] else v#Vec(v)[j+1]
           else DefaultVecElem()),
        l))
}

function {:inline} ConcatVec<T>(v1: Vec T, v2: Vec T): Vec T {
    (var l1, m1, l2, m2 := l#Vec(v1), v#Vec(v1), l#Vec(v2), v#Vec(v2);
    Vec(
        (lambda i: int ::
          if i >= 0 && i < l1 + l2 then
            if i < l1 then m1[i] else m2[i - l1]
          else DefaultVecElem()),
        l1 + l2))
}

function {:inline} ReverseVec<T>(v: Vec T): Vec T {
    (var l := l#Vec(v);
    Vec(
        (lambda i: int :: if 0 <= i && i < l then v#Vec(v)[l - i - 1] else DefaultVecElem()),
        l))
}

function {:inline} SliceVec<T>(v: Vec T, i: int, j: int): Vec T {
    (var m := v#Vec(v);
    Vec(
        (lambda k:int ::
          if 0 <= k && k < j - i then
            m[i + k]
          else
            DefaultVecElem()),
        (if j - i < 0 then 0 else j - i)))
}


function {:inline} UpdateVec<T>(v: Vec T, i: int, elem: T): Vec T {
    Vec(v#Vec(v)[i := elem], l#Vec(v))
}

function {:inline} SwapVec<T>(v: Vec T, i: int, j: int): Vec T {
    (var m := v#Vec(v);
    Vec(m[i := m[j]][j := m[i]], l#Vec(v)))
}

function {:inline} ContainsVec<T>(v: Vec T, e: T): bool {
    (var l := l#Vec(v);
    (exists i: int :: InRangeVec(v, i) && v#Vec(v)[i] == e))
}

function IndexOfVec<T>(v: Vec T, e: T): int;
axiom {:ctor "Vec"} (forall<T> v: Vec T, e: T :: {IndexOfVec(v, e)}
    (var i := IndexOfVec(v,e);
     if (!ContainsVec(v, e)) then i == -1
     else InRangeVec(v, i) && ReadVec(v, i) == e &&
        (forall j: int :: j >= 0 && j < i ==> ReadVec(v, j) != e)));

// This function should stay non-inlined as it guards many quantifiers
// over vectors. It appears important to have this uninterpreted for
// quantifier triggering.
function InRangeVec<T>(v: Vec T, i: int): bool {
    i >= 0 && i < LenVec(v)
}

// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

// Boogie model for multisets, based on Boogie arrays. This theory assumes extensional equality for element types.

type {:datatype} Multiset _;
function {:constructor} Multiset<T>(v: [T]int, l: int): Multiset T;

function {:builtin "MapConst"} MapConstMultiset<T>(l: int): [T]int;

function {:inline} EmptyMultiset<T>(): Multiset T {
    Multiset(MapConstMultiset(0), 0)
}

function {:inline} LenMultiset<T>(s: Multiset T): int {
    l#Multiset(s)
}

function {:inline} ExtendMultiset<T>(s: Multiset T, v: T): Multiset T {
    (var len := l#Multiset(s);
    (var cnt := v#Multiset(s)[v];
    Multiset(v#Multiset(s)[v := (cnt + 1)], len + 1)))
}

// This function returns (s1 - s2). This function assumes that s2 is a subset of s1.
function {:inline} SubtractMultiset<T>(s1: Multiset T, s2: Multiset T): Multiset T {
    (var len1 := l#Multiset(s1);
    (var len2 := l#Multiset(s2);
    Multiset((lambda v:T :: v#Multiset(s1)[v]-v#Multiset(s2)[v]), len1-len2)))
}

function {:inline} IsEmptyMultiset<T>(s: Multiset T): bool {
    (l#Multiset(s) == 0) &&
    (forall v: T :: v#Multiset(s)[v] == 0)
}

function {:inline} IsSubsetMultiset<T>(s1: Multiset T, s2: Multiset T): bool {
    (l#Multiset(s1) <= l#Multiset(s2)) &&
    (forall v: T :: v#Multiset(s1)[v] <= v#Multiset(s2)[v])
}

function {:inline} ContainsMultiset<T>(s: Multiset T, v: T): bool {
    v#Multiset(s)[v] > 0
}



// ============================================================================================
// Primitive Types

const $MAX_U8: int;
axiom $MAX_U8 == 255;
const $MAX_U64: int;
axiom $MAX_U64 == 18446744073709551615;
const $MAX_U128: int;
axiom $MAX_U128 == 340282366920938463463374607431768211455;

type {:datatype} $Range;
function {:constructor} $Range(lb: int, ub: int): $Range;

function {:inline} $IsValid'bool'(v: bool): bool {
  true
}

function $IsValid'u8'(v: int): bool {
  v >= 0 && v <= $MAX_U8
}

function $IsValid'u64'(v: int): bool {
  v >= 0 && v <= $MAX_U64
}

function $IsValid'u128'(v: int): bool {
  v >= 0 && v <= $MAX_U128
}

function $IsValid'num'(v: int): bool {
  true
}

function $IsValid'address'(v: int): bool {
  // TODO: restrict max to representable addresses?
  v >= 0
}

function {:inline} $IsValidRange(r: $Range): bool {
   $IsValid'u64'(lb#$Range(r)) &&  $IsValid'u64'(ub#$Range(r))
}

// Intentionally not inlined so it serves as a trigger in quantifiers.
function $InRange(r: $Range, i: int): bool {
   lb#$Range(r) <= i && i < ub#$Range(r)
}


function {:inline} $IsEqual'u8'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u64'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u128'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'num'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'address'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'bool'(x: bool, y: bool): bool {
    x == y
}

// ============================================================================================
// Memory

type {:datatype} $Location;

// A global resource location within the statically known resource type's memory,
// where `a` is an address.
function {:constructor} $Global(a: int): $Location;

// A local location. `i` is the unique index of the local.
function {:constructor} $Local(i: int): $Location;

// The location of a reference outside of the verification scope, for example, a `&mut` parameter
// of the function being verified. References with these locations don't need to be written back
// when mutation ends.
function {:constructor} $Param(i: int): $Location;


// A mutable reference which also carries its current value. Since mutable references
// are single threaded in Move, we can keep them together and treat them as a value
// during mutation until the point they are stored back to their original location.
type {:datatype} $Mutation _;
function {:constructor} $Mutation<T>(l: $Location, p: Vec int, v: T): $Mutation T;

// Representation of memory for a given type.
type {:datatype} $Memory _;
function {:constructor} $Memory<T>(domain: [int]bool, contents: [int]T): $Memory T;

function {:builtin "MapConst"} $ConstMemoryDomain(v: bool): [int]bool;
function {:builtin "MapConst"} $ConstMemoryContent<T>(v: T): [int]T;
axiom $ConstMemoryDomain(false) == (lambda i: int :: false);
axiom $ConstMemoryDomain(true) == (lambda i: int :: true);


// Dereferences a mutation.
function {:inline} $Dereference<T>(ref: $Mutation T): T {
    v#$Mutation(ref)
}

// Update the value of a mutation.
function {:inline} $UpdateMutation<T>(m: $Mutation T, v: T): $Mutation T {
    $Mutation(l#$Mutation(m), p#$Mutation(m), v)
}

function {:inline} $ChildMutation<T1, T2>(m: $Mutation T1, offset: int, v: T2): $Mutation T2 {
    $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), offset), v)
}

// Return true of the mutation is a parent of a child which was derived with the given edge offset. This
// is used to implement write-back choices.
function {:inline} $IsParentMutation<T1, T2>(parent: $Mutation T1, edge: int, child: $Mutation T2 ): bool {
    l#$Mutation(parent) == l#$Mutation(child) &&
    (var pp := p#$Mutation(parent);
    (var cp := p#$Mutation(child);
    (var pl := LenVec(pp);
    (var cl := LenVec(cp);
     cl == pl + 1 &&
     (forall i: int:: i >= 0 && i < pl ==> ReadVec(pp, i) ==  ReadVec(cp, i)) &&
     $EdgeMatches(ReadVec(cp, pl), edge)
    ))))
}

// Return true of the mutation is a parent of a child, for hyper edge.
function {:inline} $IsParentMutationHyper<T1, T2>(parent: $Mutation T1, hyper_edge: Vec int, child: $Mutation T2 ): bool {
    l#$Mutation(parent) == l#$Mutation(child) &&
    (var pp := p#$Mutation(parent);
    (var cp := p#$Mutation(child);
    (var pl := LenVec(pp);
    (var cl := LenVec(cp);
    (var el := LenVec(hyper_edge);
     cl == pl + el &&
     (forall i: int:: i >= 0 && i < pl ==> ReadVec(pp, i) == ReadVec(cp, i)) &&
     (forall i: int:: i >= 0 && i < el ==> $EdgeMatches(ReadVec(cp, pl + i), ReadVec(hyper_edge, i)))
    )))))
}

function {:inline} $EdgeMatches(edge: int, edge_pattern: int): bool {
    edge_pattern == -1 // wildcard
    || edge_pattern == edge
}



function {:inline} $SameLocation<T1, T2>(m1: $Mutation T1, m2: $Mutation T2): bool {
    l#$Mutation(m1) == l#$Mutation(m2)
}

function {:inline} $HasGlobalLocation<T>(m: $Mutation T): bool {
    is#$Global(l#$Mutation(m))
}

function {:inline} $HasLocalLocation<T>(m: $Mutation T, idx: int): bool {
    l#$Mutation(m) == $Local(idx)
}

function {:inline} $GlobalLocationAddress<T>(m: $Mutation T): int {
    a#$Global(l#$Mutation(m))
}



// Tests whether resource exists.
function {:inline} $ResourceExists<T>(m: $Memory T, addr: int): bool {
    domain#$Memory(m)[addr]
}

// Obtains Value of given resource.
function {:inline} $ResourceValue<T>(m: $Memory T, addr: int): T {
    contents#$Memory(m)[addr]
}

// Update resource.
function {:inline} $ResourceUpdate<T>(m: $Memory T, a: int, v: T): $Memory T {
    $Memory(domain#$Memory(m)[a := true], contents#$Memory(m)[a := v])
}

// Remove resource.
function {:inline} $ResourceRemove<T>(m: $Memory T, a: int): $Memory T {
    $Memory(domain#$Memory(m)[a := false], contents#$Memory(m))
}

// Copies resource from memory s to m.
function {:inline} $ResourceCopy<T>(m: $Memory T, s: $Memory T, a: int): $Memory T {
    $Memory(domain#$Memory(m)[a := domain#$Memory(s)[a]],
            contents#$Memory(m)[a := contents#$Memory(s)[a]])
}



// ============================================================================================
// Abort Handling

var $abort_flag: bool;
var $abort_code: int;

function {:inline} $process_abort_code(code: int): int {
    code
}

const $EXEC_FAILURE_CODE: int;
axiom $EXEC_FAILURE_CODE == -1;

// TODO(wrwg): currently we map aborts of native functions like those for vectors also to
//   execution failure. This may need to be aligned with what the runtime actually does.

procedure {:inline 1} $ExecFailureAbort() {
    $abort_flag := true;
    $abort_code := $EXEC_FAILURE_CODE;
}

procedure {:inline 1} $InitVerification() {
    // Set abort_flag to false, and havoc abort_code
    $abort_flag := false;
    havoc $abort_code;
    // Initialize event store
    call $InitEventStore();
}

// ============================================================================================
// Instructions


procedure {:inline 1} $CastU8(src: int) returns (dst: int)
{
    if (src > $MAX_U8) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $CastU64(src: int) returns (dst: int)
{
    if (src > $MAX_U64) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $CastU128(src: int) returns (dst: int)
{
    if (src > $MAX_U128) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $AddU8(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U8) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU64(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U64) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU64_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $AddU128(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U128) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU128_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $Sub(src1: int, src2: int) returns (dst: int)
{
    if (src1 < src2) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 - src2;
}

// Note that *not* inlining the shl/shr functions avoids timeouts. It appears that Z3 can reason
// better about this if it is an axiomatized function.
function $shl(src1: int, p: int): int {
    if p == 8 then src1 * 256
    else if p == 16 then src1 * 65536
    else if p == 32 then src1 * 4294967296
    else if p == 64 then src1 * 18446744073709551616
    // Value is undefined, otherwise.
    else -1
}

function $shr(src1: int, p: int): int {
    if p == 8 then src1 div 256
    else if p == 16 then src1 div 65536
    else if p == 32 then src1 div 4294967296
    else if p == 64 then src1 div 18446744073709551616
    // Value is undefined, otherwise.
    else -1
}

// TODO: fix this and $Shr to drop bits on overflow. Requires $Shl8, $Shl64, and $Shl128
procedure {:inline 1} $Shl(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    res := $shl(src1, src2);
    assert res >= 0;   // restriction: shift argument must be 8, 16, 32, or 64
    dst := res;
}

procedure {:inline 1} $Shr(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    res := $shr(src1, src2);
    assert res >= 0;   // restriction: shift argument must be 8, 16, 32, or 64
    dst := res;
}

procedure {:inline 1} $MulU8(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U8) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU64(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U64) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU128(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U128) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $Div(src1: int, src2: int) returns (dst: int)
{
    if (src2 == 0) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 div src2;
}

procedure {:inline 1} $Mod(src1: int, src2: int) returns (dst: int)
{
    if (src2 == 0) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 mod src2;
}

procedure {:inline 1} $ArithBinaryUnimplemented(src1: int, src2: int) returns (dst: int);

procedure {:inline 1} $Lt(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 < src2;
}

procedure {:inline 1} $Gt(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 > src2;
}

procedure {:inline 1} $Le(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 <= src2;
}

procedure {:inline 1} $Ge(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 >= src2;
}

procedure {:inline 1} $And(src1: bool, src2: bool) returns (dst: bool)
{
    dst := src1 && src2;
}

procedure {:inline 1} $Or(src1: bool, src2: bool) returns (dst: bool)
{
    dst := src1 || src2;
}

procedure {:inline 1} $Not(src: bool) returns (dst: bool)
{
    dst := !src;
}

// Pack and Unpack are auto-generated for each type T


// ==================================================================================
// Native Vector

function {:inline} $SliceVecByRange<T>(v: Vec T, r: $Range): Vec T {
    SliceVec(v, lb#$Range(r), ub#$Range(r))
}

// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `u8`

// Not inlined. It appears faster this way.
function $IsEqual'vec'u8''(v1: Vec (int), v2: Vec (int)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'u8'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsValid'vec'u8''(v: Vec (int)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'u8'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'u8'(v: Vec (int), e: int): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'u8'(ReadVec(v, i), e))
}

function $IndexOfVec'u8'(v: Vec (int), e: int): int;
axiom (forall v: Vec (int), e: int:: {$IndexOfVec'u8'(v, e)}
    (var i := $IndexOfVec'u8'(v, e);
     if (!$ContainsVec'u8'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'u8'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'u8'(ReadVec(v, j), e))));


function {:inline} $RangeVec'u8'(v: Vec (int)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'u8'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_Vector_empty'u8'() returns (v: Vec (int)) {
    v := EmptyVec();
}

function {:inline} $1_Vector_$empty'u8'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_Vector_is_empty'u8'(v: Vec (int)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_Vector_push_back'u8'(m: $Mutation (Vec (int)), val: int) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_Vector_$push_back'u8'(v: Vec (int), val: int): Vec (int) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_Vector_pop_back'u8'(m: $Mutation (Vec (int))) returns (e: int, m': $Mutation (Vec (int))) {
    var v: Vec (int);
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_Vector_append'u8'(m: $Mutation (Vec (int)), other: Vec (int)) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_Vector_reverse'u8'(m: $Mutation (Vec (int))) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_Vector_length'u8'(v: Vec (int)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_Vector_$length'u8'(v: Vec (int)): int {
    LenVec(v)
}

procedure {:inline 1} $1_Vector_borrow'u8'(v: Vec (int), i: int) returns (dst: int) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_Vector_$borrow'u8'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_Vector_borrow_mut'u8'(m: $Mutation (Vec (int)), index: int)
returns (dst: $Mutation (int), m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_Vector_$borrow_mut'u8'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_Vector_destroy_empty'u8'(v: Vec (int)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_Vector_swap'u8'(m: $Mutation (Vec (int)), i: int, j: int) returns (m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_Vector_$swap'u8'(v: Vec (int), i: int, j: int): Vec (int) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_Vector_remove'u8'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
{
    var v: Vec (int);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_Vector_swap_remove'u8'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
{
    var len: int;
    var v: Vec (int);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_Vector_contains'u8'(v: Vec (int), e: int) returns (res: bool)  {
    res := $ContainsVec'u8'(v, e);
}

procedure {:inline 1}
$1_Vector_index_of'u8'(v: Vec (int), e: int) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'u8'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ==================================================================================
// Native Hash

// Hash is modeled as an otherwise uninterpreted injection.
// In truth, it is not an injection since the domain has greater cardinality
// (arbitrary length vectors) than the co-domain (vectors of length 32).  But it is
// common to assume in code there are no hash collisions in practice.  Fortunately,
// Boogie is not smart enough to recognized that there is an inconsistency.
// FIXME: If we were using a reliable extensional theory of arrays, and if we could use ==
// instead of $IsEqual, we might be able to avoid so many quantified formulas by
// using a sha2_inverse function in the ensures conditions of Hash_sha2_256 to
// assert that sha2/3 are injections without using global quantified axioms.


function $1_Hash_sha2(val: Vec int): Vec int;

// This says that Hash_sha2 is bijective.
axiom (forall v1,v2: Vec int :: {$1_Hash_sha2(v1), $1_Hash_sha2(v2)}
       $IsEqual'vec'u8''(v1, v2) <==> $IsEqual'vec'u8''($1_Hash_sha2(v1), $1_Hash_sha2(v2)));

procedure $1_Hash_sha2_256(val: Vec int) returns (res: Vec int);
ensures res == $1_Hash_sha2(val);     // returns Hash_sha2 Value
ensures $IsValid'vec'u8''(res);    // result is a legal vector of U8s.
ensures LenVec(res) == 32;               // result is 32 bytes.

// Spec version of Move native function.
function {:inline} $1_Hash_$sha2_256(val: Vec int): Vec int {
    $1_Hash_sha2(val)
}

// similarly for Hash_sha3
function $1_Hash_sha3(val: Vec int): Vec int;

axiom (forall v1,v2: Vec int :: {$1_Hash_sha3(v1), $1_Hash_sha3(v2)}
       $IsEqual'vec'u8''(v1, v2) <==> $IsEqual'vec'u8''($1_Hash_sha3(v1), $1_Hash_sha3(v2)));

procedure $1_Hash_sha3_256(val: Vec int) returns (res: Vec int);
ensures res == $1_Hash_sha3(val);     // returns Hash_sha3 Value
ensures $IsValid'vec'u8''(res);    // result is a legal vector of U8s.
ensures LenVec(res) == 32;               // result is 32 bytes.

// Spec version of Move native function.
function {:inline} $1_Hash_$sha3_256(val: Vec int): Vec int {
    $1_Hash_sha3(val)
}

// ==================================================================================
// Native diem_account

procedure {:inline 1} $1_DiemAccount_create_signer(
  addr: int
) returns (signer: $signer) {
    // A signer is currently identical to an address.
    signer := $signer(addr);
}

procedure {:inline 1} $1_DiemAccount_destroy_signer(
  signer: $signer
) {
  return;
}

// ==================================================================================
// Native Signer

type {:datatype} $signer;
function {:constructor} $signer($addr: int): $signer;
function {:inline} $IsValid'signer'(s: $signer): bool {
    $IsValid'address'($addr#$signer(s))
}
function {:inline} $IsEqual'signer'(s1: $signer, s2: $signer): bool {
    s1 == s2
}

procedure {:inline 1} $1_Signer_borrow_address(signer: $signer) returns (res: int) {
    res := $addr#$signer(signer);
}

function {:inline} $1_Signer_$borrow_address(signer: $signer): int
{
    $addr#$signer(signer)
}

function $1_Signer_is_txn_signer(s: $signer): bool;

function $1_Signer_is_txn_signer_addr(a: int): bool;


// ==================================================================================
// Native signature

// Signature related functionality is handled via uninterpreted functions. This is sound
// currently because we verify every code path based on signature verification with
// an arbitrary interpretation.

function $1_Signature_$ed25519_validate_pubkey(public_key: Vec int): bool;
function $1_Signature_$ed25519_verify(signature: Vec int, public_key: Vec int, message: Vec int): bool;

// Needed because we do not have extensional equality:
axiom (forall k1, k2: Vec int ::
    {$1_Signature_$ed25519_validate_pubkey(k1), $1_Signature_$ed25519_validate_pubkey(k2)}
    $IsEqual'vec'u8''(k1, k2) ==> $1_Signature_$ed25519_validate_pubkey(k1) == $1_Signature_$ed25519_validate_pubkey(k2));
axiom (forall s1, s2, k1, k2, m1, m2: Vec int ::
    {$1_Signature_$ed25519_verify(s1, k1, m1), $1_Signature_$ed25519_verify(s2, k2, m2)}
    $IsEqual'vec'u8''(s1, s2) && $IsEqual'vec'u8''(k1, k2) && $IsEqual'vec'u8''(m1, m2)
    ==> $1_Signature_$ed25519_verify(s1, k1, m1) == $1_Signature_$ed25519_verify(s2, k2, m2));


procedure {:inline 1} $1_Signature_ed25519_validate_pubkey(public_key: Vec int) returns (res: bool) {
    res := $1_Signature_$ed25519_validate_pubkey(public_key);
}

procedure {:inline 1} $1_Signature_ed25519_verify(
        signature: Vec int, public_key: Vec int, message: Vec int) returns (res: bool) {
    res := $1_Signature_$ed25519_verify(signature, public_key, message);
}


// ==================================================================================
// Native BCS::serialize


// ==================================================================================
// Native Event module



procedure {:inline 1} $InitEventStore() {
}



//==================================
// Begin Translation



// Given Types for Type Parameters


// spec fun at ../../../../language/move-stdlib/sources/Signer.move:12:5+77
function {:inline} $1_Signer_$address_of(s: $signer): int {
    $1_Signer_$borrow_address(s)
}

// fun Signer::address_of [baseline] at ../../../../language/move-stdlib/sources/Signer.move:12:5+77
procedure {:inline 1} $1_Signer_address_of(_$t0: $signer) returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t0: $signer;
    var $temp_0'address': int;
    var $temp_0'signer': $signer;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[s]($t0) at ../../../../language/move-stdlib/sources/Signer.move:12:5+1
    assume {:print "$at(10,389,390)"} true;
    assume {:print "$track_local(0,0,0):", $t0} $t0 == $t0;

    // $t1 := Signer::borrow_address($t0) on_abort goto L2 with $t2 at ../../../../language/move-stdlib/sources/Signer.move:13:10+17
    assume {:print "$at(10,443,460)"} true;
    call $t1 := $1_Signer_borrow_address($t0);
    if ($abort_flag) {
        assume {:print "$at(10,443,460)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(0,0):", $t2} $t2 == $t2;
        goto L2;
    }

    // trace_return[0]($t1) at ../../../../language/move-stdlib/sources/Signer.move:13:9+18
    assume {:print "$track_return(0,0,0):", $t1} $t1 == $t1;

    // label L1 at ../../../../language/move-stdlib/sources/Signer.move:14:5+1
    assume {:print "$at(10,465,466)"} true;
L1:

    // return $t1 at ../../../../language/move-stdlib/sources/Signer.move:14:5+1
    $ret0 := $t1;
    return;

    // label L2 at ../../../../language/move-stdlib/sources/Signer.move:14:5+1
L2:

    // abort($t2) at ../../../../language/move-stdlib/sources/Signer.move:14:5+1
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun CoreAddresses::assert_currency_info [verification] at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:69:5+161
procedure {:timeLimit 40} $1_CoreAddresses_assert_currency_info$verify(_$t0: $signer) returns ()
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t3: int;
    var $t4: bool;
    var $t5: int;
    var $t6: int;
    var $t0: $signer;
    var $temp_0'signer': $signer;
    $t0 := _$t0;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:69:5+1
    assume {:print "$at(15,2766,2767)"} true;
    assume $IsValid'signer'($t0) && $1_Signer_is_txn_signer($t0) && $1_Signer_is_txn_signer_addr($addr#$signer($t0));

    // trace_local[account]($t0) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:69:5+1
    assume {:print "$track_local(2,0,0):", $t0} $t0 == $t0;

    // $t1 := Signer::address_of($t0) on_abort goto L3 with $t2 at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:70:17+27
    assume {:print "$at(15,2834,2861)"} true;
    call $t1 := $1_Signer_address_of($t0);
    if ($abort_flag) {
        assume {:print "$at(15,2834,2861)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(2,0):", $t2} $t2 == $t2;
        goto L3;
    }

    // $t3 := 0xa550c18 at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:70:48+13
    $t3 := 173345816;
    assume $IsValid'address'($t3);

    // $t4 := ==($t1, $t3) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:70:45+2
    $t4 := $IsEqual'address'($t1, $t3);

    // if ($t4) goto L0 else goto L1 at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:70:9+95
    if ($t4) { goto L0; } else { goto L1; }

    // label L1 at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:70:88+14
L1:

    // $t5 := 3 at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:70:88+14
    $t5 := 3;
    assume $IsValid'u64'($t5);

    // $t6 := opaque begin: Errors::requires_address($t5) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:70:63+40

    // assume WellFormed($t6) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:70:63+40
    assume $IsValid'u64'($t6);

    // assume Eq<u64>($t6, 2) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:70:63+40
    assume $IsEqual'u64'($t6, 2);

    // $t6 := opaque end: Errors::requires_address($t5) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:70:63+40

    // trace_abort($t6) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:70:9+95
    assume {:print "$at(15,2826,2921)"} true;
    assume {:print "$track_abort(2,0):", $t6} $t6 == $t6;

    // $t2 := move($t6) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:70:9+95
    $t2 := $t6;

    // goto L3 at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:70:9+95
    goto L3;

    // label L0 at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:70:9+95
L0:

    // label L2 at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:71:5+1
    assume {:print "$at(15,2926,2927)"} true;
L2:

    // assert Not(Neq<address>(Signer::$address_of[]($t0), a550c18)) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:80:9+85
    assume {:print "$at(15,3197,3282)"} true;
    assert {:msg "assert_failed(15,3197,3282): function does not abort under this condition"}
      !!$IsEqual'address'($1_Signer_$address_of($t0), 173345816);

    // return () at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:80:9+85
    return;

    // label L3 at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:71:5+1
    assume {:print "$at(15,2926,2927)"} true;
L3:

    // assert Neq<address>(Signer::$address_of[]($t0), a550c18) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:72:5+97
    assume {:print "$at(15,2932,3029)"} true;
    assert {:msg "assert_failed(15,2932,3029): abort not covered by any of the `aborts_if` clauses"}
      !$IsEqual'address'($1_Signer_$address_of($t0), 173345816);

    // assert And(Neq<address>(Signer::$address_of[]($t0), a550c18), Eq(2, $t2)) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:72:5+97
    assert {:msg "assert_failed(15,2932,3029): abort code not covered by any of the `aborts_if` or `aborts_with` clauses"}
      (!$IsEqual'address'($1_Signer_$address_of($t0), 173345816) && $IsEqual'num'(2, $t2));

    // abort($t2) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:72:5+97
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun CoreAddresses::assert_diem_root [verification] at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:20:5+149
procedure {:timeLimit 40} $1_CoreAddresses_assert_diem_root$verify(_$t0: $signer) returns ()
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t3: int;
    var $t4: bool;
    var $t5: int;
    var $t6: int;
    var $t0: $signer;
    var $temp_0'signer': $signer;
    $t0 := _$t0;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:20:5+1
    assume {:print "$at(15,971,972)"} true;
    assume $IsValid'signer'($t0) && $1_Signer_is_txn_signer($t0) && $1_Signer_is_txn_signer_addr($addr#$signer($t0));

    // trace_local[account]($t0) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:20:5+1
    assume {:print "$track_local(2,1,0):", $t0} $t0 == $t0;

    // $t1 := Signer::address_of($t0) on_abort goto L3 with $t2 at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:21:17+27
    assume {:print "$at(15,1035,1062)"} true;
    call $t1 := $1_Signer_address_of($t0);
    if ($abort_flag) {
        assume {:print "$at(15,1035,1062)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(2,1):", $t2} $t2 == $t2;
        goto L3;
    }

    // $t3 := 0xa550c18 at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:21:48+9
    $t3 := 173345816;
    assume $IsValid'address'($t3);

    // $t4 := ==($t1, $t3) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:21:45+2
    $t4 := $IsEqual'address'($t1, $t3);

    // if ($t4) goto L0 else goto L1 at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:21:9+87
    if ($t4) { goto L0; } else { goto L1; }

    // label L1 at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:21:84+10
L1:

    // $t5 := 0 at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:21:84+10
    $t5 := 0;
    assume $IsValid'u64'($t5);

    // $t6 := opaque begin: Errors::requires_address($t5) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:21:59+36

    // assume WellFormed($t6) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:21:59+36
    assume $IsValid'u64'($t6);

    // assume Eq<u64>($t6, 2) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:21:59+36
    assume $IsEqual'u64'($t6, 2);

    // $t6 := opaque end: Errors::requires_address($t5) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:21:59+36

    // trace_abort($t6) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:21:9+87
    assume {:print "$at(15,1027,1114)"} true;
    assume {:print "$track_abort(2,1):", $t6} $t6 == $t6;

    // $t2 := move($t6) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:21:9+87
    $t2 := $t6;

    // goto L3 at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:21:9+87
    goto L3;

    // label L0 at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:21:9+87
L0:

    // label L2 at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:22:5+1
    assume {:print "$at(15,1119,1120)"} true;
L2:

    // assert Not(Neq<address>(Signer::$address_of[]($t0), a550c18)) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:31:9+81
    assume {:print "$at(15,1380,1461)"} true;
    assert {:msg "assert_failed(15,1380,1461): function does not abort under this condition"}
      !!$IsEqual'address'($1_Signer_$address_of($t0), 173345816);

    // return () at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:31:9+81
    return;

    // label L3 at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:22:5+1
    assume {:print "$at(15,1119,1120)"} true;
L3:

    // assert Neq<address>(Signer::$address_of[]($t0), a550c18) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:23:5+89
    assume {:print "$at(15,1125,1214)"} true;
    assert {:msg "assert_failed(15,1125,1214): abort not covered by any of the `aborts_if` clauses"}
      !$IsEqual'address'($1_Signer_$address_of($t0), 173345816);

    // assert And(Neq<address>(Signer::$address_of[]($t0), a550c18), Eq(2, $t2)) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:23:5+89
    assert {:msg "assert_failed(15,1125,1214): abort code not covered by any of the `aborts_if` or `aborts_with` clauses"}
      (!$IsEqual'address'($1_Signer_$address_of($t0), 173345816) && $IsEqual'num'(2, $t2));

    // abort($t2) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:23:5+89
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun CoreAddresses::assert_treasury_compliance [verification] at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:35:5+213
procedure {:timeLimit 40} $1_CoreAddresses_assert_treasury_compliance$verify(_$t0: $signer) returns ()
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t3: int;
    var $t4: bool;
    var $t5: int;
    var $t6: int;
    var $t0: $signer;
    var $temp_0'signer': $signer;
    $t0 := _$t0;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:35:5+1
    assume {:print "$at(15,1541,1542)"} true;
    assume $IsValid'signer'($t0) && $1_Signer_is_txn_signer($t0) && $1_Signer_is_txn_signer_addr($addr#$signer($t0));

    // trace_local[account]($t0) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:35:5+1
    assume {:print "$track_local(2,2,0):", $t0} $t0 == $t0;

    // $t1 := Signer::address_of($t0) on_abort goto L3 with $t2 at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:37:13+27
    assume {:print "$at(15,1628,1655)"} true;
    call $t1 := $1_Signer_address_of($t0);
    if ($abort_flag) {
        assume {:print "$at(15,1628,1655)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(2,2):", $t2} $t2 == $t2;
        goto L3;
    }

    // $t3 := 0xb1e55ed at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:37:44+19
    $t3 := 186537453;
    assume $IsValid'address'($t3);

    // $t4 := ==($t1, $t3) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:37:41+2
    $t4 := $IsEqual'address'($t1, $t3);

    // if ($t4) goto L0 else goto L1 at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:36:9+141
    assume {:print "$at(15,1607,1748)"} true;
    if ($t4) { goto L0; } else { goto L1; }

    // label L1 at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:38:38+20
    assume {:print "$at(15,1717,1737)"} true;
L1:

    // $t5 := 1 at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:38:38+20
    $t5 := 1;
    assume $IsValid'u64'($t5);

    // $t6 := opaque begin: Errors::requires_address($t5) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:38:13+46

    // assume WellFormed($t6) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:38:13+46
    assume $IsValid'u64'($t6);

    // assume Eq<u64>($t6, 2) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:38:13+46
    assume $IsEqual'u64'($t6, 2);

    // $t6 := opaque end: Errors::requires_address($t5) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:38:13+46

    // trace_abort($t6) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:36:9+141
    assume {:print "$at(15,1607,1748)"} true;
    assume {:print "$track_abort(2,2):", $t6} $t6 == $t6;

    // $t2 := move($t6) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:36:9+141
    $t2 := $t6;

    // goto L3 at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:36:9+141
    goto L3;

    // label L0 at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:36:9+141
L0:

    // label L2 at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:40:5+1
    assume {:print "$at(15,1753,1754)"} true;
L2:

    // assert Not(Neq<address>(Signer::$address_of[]($t0), b1e55ed)) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:49:9+103
    assume {:print "$at(15,2054,2157)"} true;
    assert {:msg "assert_failed(15,2054,2157): function does not abort under this condition"}
      !!$IsEqual'address'($1_Signer_$address_of($t0), 186537453);

    // return () at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:49:9+103
    return;

    // label L3 at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:40:5+1
    assume {:print "$at(15,1753,1754)"} true;
L3:

    // assert Neq<address>(Signer::$address_of[]($t0), b1e55ed) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:41:5+109
    assume {:print "$at(15,1759,1868)"} true;
    assert {:msg "assert_failed(15,1759,1868): abort not covered by any of the `aborts_if` clauses"}
      !$IsEqual'address'($1_Signer_$address_of($t0), 186537453);

    // assert And(Neq<address>(Signer::$address_of[]($t0), b1e55ed), Eq(2, $t2)) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:41:5+109
    assert {:msg "assert_failed(15,1759,1868): abort code not covered by any of the `aborts_if` or `aborts_with` clauses"}
      (!$IsEqual'address'($1_Signer_$address_of($t0), 186537453) && $IsEqual'num'(2, $t2));

    // abort($t2) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:41:5+109
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun CoreAddresses::assert_vm [verification] at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:54:5+137
procedure {:timeLimit 40} $1_CoreAddresses_assert_vm$verify(_$t0: $signer) returns ()
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t3: int;
    var $t4: bool;
    var $t5: int;
    var $t6: int;
    var $t0: $signer;
    var $temp_0'signer': $signer;
    $t0 := _$t0;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:54:5+1
    assume {:print "$at(15,2229,2230)"} true;
    assume $IsValid'signer'($t0) && $1_Signer_is_txn_signer($t0) && $1_Signer_is_txn_signer_addr($addr#$signer($t0));

    // trace_local[account]($t0) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:54:5+1
    assume {:print "$track_local(2,3,0):", $t0} $t0 == $t0;

    // $t1 := Signer::address_of($t0) on_abort goto L3 with $t2 at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:55:17+27
    assume {:print "$at(15,2286,2313)"} true;
    call $t1 := $1_Signer_address_of($t0);
    if ($abort_flag) {
        assume {:print "$at(15,2286,2313)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(2,3):", $t2} $t2 == $t2;
        goto L3;
    }

    // $t3 := 0x0 at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:55:48+11
    $t3 := 0;
    assume $IsValid'address'($t3);

    // $t4 := ==($t1, $t3) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:55:45+2
    $t4 := $IsEqual'address'($t1, $t3);

    // if ($t4) goto L0 else goto L1 at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:55:9+82
    if ($t4) { goto L0; } else { goto L1; }

    // label L1 at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:55:86+3
L1:

    // $t5 := 2 at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:55:86+3
    $t5 := 2;
    assume $IsValid'u64'($t5);

    // $t6 := opaque begin: Errors::requires_address($t5) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:55:61+29

    // assume WellFormed($t6) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:55:61+29
    assume $IsValid'u64'($t6);

    // assume Eq<u64>($t6, 2) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:55:61+29
    assume $IsEqual'u64'($t6, 2);

    // $t6 := opaque end: Errors::requires_address($t5) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:55:61+29

    // trace_abort($t6) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:55:9+82
    assume {:print "$at(15,2278,2360)"} true;
    assume {:print "$track_abort(2,3):", $t6} $t6 == $t6;

    // $t2 := move($t6) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:55:9+82
    $t2 := $t6;

    // goto L3 at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:55:9+82
    goto L3;

    // label L0 at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:55:9+82
L0:

    // label L2 at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:56:5+1
    assume {:print "$at(15,2365,2366)"} true;
L2:

    // assert Not(Neq<address>(Signer::$address_of[]($t0), 0)) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:65:9+83
    assume {:print "$at(15,2609,2692)"} true;
    assert {:msg "assert_failed(15,2609,2692): function does not abort under this condition"}
      !!$IsEqual'address'($1_Signer_$address_of($t0), 0);

    // return () at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:65:9+83
    return;

    // label L3 at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:56:5+1
    assume {:print "$at(15,2365,2366)"} true;
L3:

    // assert Neq<address>(Signer::$address_of[]($t0), 0) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:57:5+76
    assume {:print "$at(15,2371,2447)"} true;
    assert {:msg "assert_failed(15,2371,2447): abort not covered by any of the `aborts_if` clauses"}
      !$IsEqual'address'($1_Signer_$address_of($t0), 0);

    // assert And(Neq<address>(Signer::$address_of[]($t0), 0), Eq(2, $t2)) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:57:5+76
    assert {:msg "assert_failed(15,2371,2447): abort code not covered by any of the `aborts_if` or `aborts_with` clauses"}
      (!$IsEqual'address'($1_Signer_$address_of($t0), 0) && $IsEqual'num'(2, $t2));

    // abort($t2) at ../../../../diem-move/diem-framework/core/sources/CoreAddresses.move:57:5+76
    $abort_code := $t2;
    $abort_flag := true;
    return;

}
