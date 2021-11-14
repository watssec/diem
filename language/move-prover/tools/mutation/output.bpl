
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
// Native Vector implementation for element type `u64`

// Not inlined. It appears faster this way.
function $IsEqual'vec'u64''(v1: Vec (int), v2: Vec (int)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'u64'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsValid'vec'u64''(v: Vec (int)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'u64'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'u64'(v: Vec (int), e: int): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'u64'(ReadVec(v, i), e))
}

function $IndexOfVec'u64'(v: Vec (int), e: int): int;
axiom (forall v: Vec (int), e: int:: {$IndexOfVec'u64'(v, e)}
    (var i := $IndexOfVec'u64'(v, e);
     if (!$ContainsVec'u64'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'u64'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'u64'(ReadVec(v, j), e))));


function {:inline} $RangeVec'u64'(v: Vec (int)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'u64'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_Vector_empty'u64'() returns (v: Vec (int)) {
    v := EmptyVec();
}

function {:inline} $1_Vector_$empty'u64'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_Vector_is_empty'u64'(v: Vec (int)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_Vector_push_back'u64'(m: $Mutation (Vec (int)), val: int) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_Vector_$push_back'u64'(v: Vec (int), val: int): Vec (int) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_Vector_pop_back'u64'(m: $Mutation (Vec (int))) returns (e: int, m': $Mutation (Vec (int))) {
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

procedure {:inline 1} $1_Vector_append'u64'(m: $Mutation (Vec (int)), other: Vec (int)) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_Vector_reverse'u64'(m: $Mutation (Vec (int))) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_Vector_length'u64'(v: Vec (int)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_Vector_$length'u64'(v: Vec (int)): int {
    LenVec(v)
}

procedure {:inline 1} $1_Vector_borrow'u64'(v: Vec (int), i: int) returns (dst: int) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_Vector_$borrow'u64'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_Vector_borrow_mut'u64'(m: $Mutation (Vec (int)), index: int)
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

function {:inline} $1_Vector_$borrow_mut'u64'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_Vector_destroy_empty'u64'(v: Vec (int)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_Vector_swap'u64'(m: $Mutation (Vec (int)), i: int, j: int) returns (m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_Vector_$swap'u64'(v: Vec (int), i: int, j: int): Vec (int) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_Vector_remove'u64'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
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

procedure {:inline 1} $1_Vector_swap_remove'u64'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
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

procedure {:inline 1} $1_Vector_contains'u64'(v: Vec (int), e: int) returns (res: bool)  {
    res := $ContainsVec'u64'(v, e);
}

procedure {:inline 1}
$1_Vector_index_of'u64'(v: Vec (int), e: int) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'u64'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
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


// fun Test::sort [verification] at ../../../../swap/src/modules/module.move:5:5+1394
procedure {:timeLimit 40} $2_Test_sort$verify(_$t0: $Mutation (Vec (int))) returns ($ret0: $Mutation (Vec (int)))
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t3: int;
    var $t4: Vec (int);
    var $t5: Vec (int);
    var $t6: Vec (int);
    var $t7: Vec (int);
    var $t8: Vec (int);
    var $t9: Vec (int);
    var $t10: int;
    var $t11: Vec (int);
    var $t12: int;
    var $t13: int;
    var $t14: int;
    var $t15: bool;
    var $t16: int;
    var $t17: int;
    var $t18: bool;
    var $t19: int;
    var $t20: int;
    var $t21: int;
    var $t22: int;
    var $t23: bool;
    var $t24: int;
    var $t25: int;
    var $t26: int;
    var $t27: int;
    var $t28: bool;
    var $t29: int;
    var $t30: int;
    var $t31: int;
    var $t32: int;
    var $t33: int;
    var $t34: int;
    var $t35: $Mutation (int);
    var $t36: $Mutation (int);
    var $t0: $Mutation (Vec (int));
    var $temp_0'u64': int;
    var $temp_0'vec'u64'': Vec (int);
    $t0 := _$t0;
    assume IsEmptyVec(p#$Mutation($t35));
    assume IsEmptyVec(p#$Mutation($t36));

    // verification entrypoint assumptions
    call $InitVerification();
    assume l#$Mutation($t0) == $Param(0);

    // bytecode translation starts here
    // assume WellFormed($t0) at ../../../../swap/src/modules/module.move:5:5+1
    assume {:print "$at(9,52,53)"} true;
    assume $IsValid'vec'u64''($Dereference($t0));

    // $t4 := read_ref($t0) at ../../../../swap/src/modules/module.move:5:5+1
    $t4 := $Dereference($t0);

    // $t5 := read_ref($t0) at ../../../../swap/src/modules/module.move:5:5+1
    $t5 := $Dereference($t0);

    // $t6 := read_ref($t0) at ../../../../swap/src/modules/module.move:5:5+1
    $t6 := $Dereference($t0);

    // $t7 := read_ref($t0) at ../../../../swap/src/modules/module.move:5:5+1
    $t7 := $Dereference($t0);

    // $t8 := read_ref($t0) at ../../../../swap/src/modules/module.move:5:5+1
    $t8 := $Dereference($t0);

    // $t9 := read_ref($t0) at ../../../../swap/src/modules/module.move:5:5+1
    $t9 := $Dereference($t0);

    // trace_local[v]($t0) at ../../../../swap/src/modules/module.move:5:5+1
    $temp_0'vec'u64'' := $Dereference($t0);
    assume {:print "$track_local(1,0,0):", $temp_0'vec'u64''} $temp_0'vec'u64'' == $temp_0'vec'u64'';

    // $t10 := 0 at ../../../../swap/src/modules/module.move:6:17+1
    assume {:print "$at(9,99,100)"} true;
    $t10 := 0;
    assume $IsValid'u64'($t10);

    // trace_local[i]($t10) at ../../../../swap/src/modules/module.move:6:13+1
    assume {:print "$track_local(1,0,1):", $t10} $t10 == $t10;

    // $t11 := read_ref($t0) at ../../../../swap/src/modules/module.move:7:32+1
    assume {:print "$at(9,133,134)"} true;
    $t11 := $Dereference($t0);

    // $t12 := Vector::length<u64>($t11) on_abort goto L18 with $t13 at ../../../../swap/src/modules/module.move:7:17+17
    call $t12 := $1_Vector_length'u64'($t11);
    if ($abort_flag) {
        assume {:print "$at(9,118,135)"} true;
        $t13 := $abort_code;
        assume {:print "$track_abort(1,0):", $t13} $t13 == $t13;
        goto L18;
    }

    // trace_local[l]($t12) at ../../../../swap/src/modules/module.move:7:13+1
    assume {:print "$track_local(1,0,3):", $t12} $t12 == $t12;

    // $t14 := 0 at ../../../../swap/src/modules/module.move:8:18+1
    assume {:print "$at(9,154,155)"} true;
    $t14 := 0;
    assume $IsValid'u64'($t14);

    // $t15 := !=($t12, $t14) at ../../../../swap/src/modules/module.move:8:15+2
    $t15 := !$IsEqual'u64'($t12, $t14);

    // if ($t15) goto L19 else goto L1 at ../../../../swap/src/modules/module.move:8:9+1295
    if ($t15) { goto L19; } else { goto L1; }

    // label L1 at ../../../../swap/src/modules/module.move:8:9+1295
L1:

    // goto L2 at ../../../../swap/src/modules/module.move:8:9+1295
    goto L2;

    // label L0 at ../../../../swap/src/modules/module.move:8:9+1295
L0:

    // destroy($t0) at ../../../../swap/src/modules/module.move:8:9+1295

    // goto L3 at ../../../../swap/src/modules/module.move:8:9+1295
    goto L3;

    // label L2 at ../../../../swap/src/modules/module.move:10:17+374
    assume {:print "$at(9,195,569)"} true;
L2:

    // assert Eq<num>(Len<u64>($t0), Len<u64>($t6)) at ../../../../swap/src/modules/module.move:11:21+32
    assume {:print "$at(9,221,253)"} true;
    assert {:msg "assert_failed(9,221,253): base case of the loop invariant does not hold"}
      $IsEqual'num'(LenVec($Dereference($t0)), LenVec($t6));

    // assert Le($t10, Len<u64>($t0)) at ../../../../swap/src/modules/module.move:12:21+22
    assume {:print "$at(9,274,296)"} true;
    assert {:msg "assert_failed(9,274,296): base case of the loop invariant does not hold"}
      ($t10 <= LenVec($Dereference($t0)));

    // assert forall p: Range(0, Sub($t12, $t10)), q: Range(Sub($t12, $t10), $t12): Le(Index($t0, p), Index($t0, q)) at ../../../../swap/src/modules/module.move:13:21+56
    assume {:print "$at(9,317,373)"} true;
    assert {:msg "assert_failed(9,317,373): base case of the loop invariant does not hold"}
      (var $range_0 := $Range(0, ($t12 - $t10)); (var $range_1 := $Range(($t12 - $t10), $t12); (forall $i_2: int, $i_3: int :: $InRange($range_0, $i_2) ==> $InRange($range_1, $i_3) ==> (var p := $i_2;
    (var q := $i_3;
    ((ReadVec($Dereference($t0), p) <= ReadVec($Dereference($t0), q))))))));

    // assert forall m: Range(Sub($t12, $t10), $t12), n: Range(Sub($t12, $t10), $t12): Implies(Le(m, n), Le(Index($t0, m), Index($t0, n))) at ../../../../swap/src/modules/module.move:14:21+67
    assume {:print "$at(9,394,461)"} true;
    assert {:msg "assert_failed(9,394,461): base case of the loop invariant does not hold"}
      (var $range_0 := $Range(($t12 - $t10), $t12); (var $range_1 := $Range(($t12 - $t10), $t12); (forall $i_2: int, $i_3: int :: $InRange($range_0, $i_2) ==> $InRange($range_1, $i_3) ==> (var m := $i_2;
    (var n := $i_3;
    (((m <= n) ==> (ReadVec($Dereference($t0), m) <= ReadVec($Dereference($t0), n)))))))));

    // havoc[val]($t10) at ../../../../swap/src/modules/module.move:14:21+67
    havoc $t10;
    assume $IsValid'u64'($t10);

    // havoc[val]($t2) at ../../../../swap/src/modules/module.move:14:21+67
    havoc $t2;
    assume $IsValid'u64'($t2);

    // havoc[val]($t16) at ../../../../swap/src/modules/module.move:14:21+67
    havoc $t16;
    assume $IsValid'u64'($t16);

    // havoc[val]($t17) at ../../../../swap/src/modules/module.move:14:21+67
    havoc $t17;
    assume $IsValid'u64'($t17);

    // havoc[val]($t18) at ../../../../swap/src/modules/module.move:14:21+67
    havoc $t18;
    assume $IsValid'bool'($t18);

    // havoc[val]($t19) at ../../../../swap/src/modules/module.move:14:21+67
    havoc $t19;
    assume $IsValid'u64'($t19);

    // havoc[val]($t20) at ../../../../swap/src/modules/module.move:14:21+67
    havoc $t20;
    assume $IsValid'u64'($t20);

    // havoc[val]($t21) at ../../../../swap/src/modules/module.move:14:21+67
    havoc $t21;
    assume $IsValid'u64'($t21);

    // havoc[val]($t22) at ../../../../swap/src/modules/module.move:14:21+67
    havoc $t22;
    assume $IsValid'u64'($t22);

    // havoc[val]($t23) at ../../../../swap/src/modules/module.move:14:21+67
    havoc $t23;
    assume $IsValid'bool'($t23);

    // havoc[val]($t24) at ../../../../swap/src/modules/module.move:14:21+67
    havoc $t24;
    assume $IsValid'u64'($t24);

    // havoc[val]($t25) at ../../../../swap/src/modules/module.move:14:21+67
    havoc $t25;
    assume $IsValid'u64'($t25);

    // havoc[val]($t26) at ../../../../swap/src/modules/module.move:14:21+67
    havoc $t26;
    assume $IsValid'u64'($t26);

    // havoc[val]($t27) at ../../../../swap/src/modules/module.move:14:21+67
    havoc $t27;
    assume $IsValid'u64'($t27);

    // havoc[val]($t28) at ../../../../swap/src/modules/module.move:14:21+67
    havoc $t28;
    assume $IsValid'bool'($t28);

    // havoc[val]($t29) at ../../../../swap/src/modules/module.move:14:21+67
    havoc $t29;
    assume $IsValid'u64'($t29);

    // havoc[val]($t30) at ../../../../swap/src/modules/module.move:14:21+67
    havoc $t30;
    assume $IsValid'u64'($t30);

    // havoc[val]($t31) at ../../../../swap/src/modules/module.move:14:21+67
    havoc $t31;
    assume $IsValid'u64'($t31);

    // havoc[val]($t32) at ../../../../swap/src/modules/module.move:14:21+67
    havoc $t32;
    assume $IsValid'u64'($t32);

    // havoc[val]($t33) at ../../../../swap/src/modules/module.move:14:21+67
    havoc $t33;
    assume $IsValid'u64'($t33);

    // havoc[val]($t34) at ../../../../swap/src/modules/module.move:14:21+67
    havoc $t34;
    assume $IsValid'u64'($t34);

    // havoc[mut]($t0) at ../../../../swap/src/modules/module.move:14:21+67
    havoc $temp_0'vec'u64'';
    $t0 := $UpdateMutation($t0, $temp_0'vec'u64'');
    assume $IsValid'vec'u64''($Dereference($t0));

    // havoc[mut_all]($t35) at ../../../../swap/src/modules/module.move:14:21+67
    havoc $t35;
    assume $IsValid'u64'($Dereference($t35));

    // havoc[mut_all]($t36) at ../../../../swap/src/modules/module.move:14:21+67
    havoc $t36;
    assume $IsValid'u64'($Dereference($t36));

    // assume Not(AbortFlag()) at ../../../../swap/src/modules/module.move:14:21+67
    assume !$abort_flag;

    // assume Eq<num>(Len<u64>($t0), Len<u64>($t4)) at ../../../../swap/src/modules/module.move:11:21+32
    assume {:print "$at(9,221,253)"} true;
    assume $IsEqual'num'(LenVec($Dereference($t0)), LenVec($t4));

    // assume Le($t10, Len<u64>($t0)) at ../../../../swap/src/modules/module.move:12:21+22
    assume {:print "$at(9,274,296)"} true;
    assume ($t10 <= LenVec($Dereference($t0)));

    // assume forall p: Range(0, Sub($t12, $t10)), q: Range(Sub($t12, $t10), $t12): Le(Index($t0, p), Index($t0, q)) at ../../../../swap/src/modules/module.move:13:21+56
    assume {:print "$at(9,317,373)"} true;
    assume (var $range_0 := $Range(0, ($t12 - $t10)); (var $range_1 := $Range(($t12 - $t10), $t12); (forall $i_2: int, $i_3: int :: $InRange($range_0, $i_2) ==> $InRange($range_1, $i_3) ==> (var p := $i_2;
    (var q := $i_3;
    ((ReadVec($Dereference($t0), p) <= ReadVec($Dereference($t0), q))))))));

    // assume forall m: Range(Sub($t12, $t10), $t12), n: Range(Sub($t12, $t10), $t12): Implies(Le(m, n), Le(Index($t0, m), Index($t0, n))) at ../../../../swap/src/modules/module.move:14:21+67
    assume {:print "$at(9,394,461)"} true;
    assume (var $range_0 := $Range(($t12 - $t10), $t12); (var $range_1 := $Range(($t12 - $t10), $t12); (forall $i_2: int, $i_3: int :: $InRange($range_0, $i_2) ==> $InRange($range_1, $i_3) ==> (var m := $i_2;
    (var n := $i_3;
    (((m <= n) ==> (ReadVec($Dereference($t0), m) <= ReadVec($Dereference($t0), n)))))))));

    // $t16 := 1 at ../../../../swap/src/modules/module.move:18:24+1
    assume {:print "$at(9,594,595)"} true;
    $t16 := 1;
    assume $IsValid'u64'($t16);

    // $t17 := +($t12, $t16) on_abort goto L18 with $t13 at ../../../../swap/src/modules/module.move:18:23+1
    call $t17 := $AddU64($t12, $t16);
    if ($abort_flag) {
        assume {:print "$at(9,593,594)"} true;
        $t13 := $abort_code;
        assume {:print "$track_abort(1,0):", $t13} $t13 == $t13;
        goto L18;
    }

    // $t18 := <($t10, $t17) at ../../../../swap/src/modules/module.move:18:20+1
    call $t18 := $Lt($t10, $t17);

    // if ($t18) goto L4 else goto L20 at ../../../../swap/src/modules/module.move:9:13+1259
    assume {:print "$at(9,171,1430)"} true;
    if ($t18) { goto L4; } else { goto L20; }

    // label L5 at ../../../../swap/src/modules/module.move:9:13+1259
L5:

    // goto L6 at ../../../../swap/src/modules/module.move:9:13+1259
    goto L6;

    // label L4 at ../../../../swap/src/modules/module.move:21:25+1
    assume {:print "$at(9,639,640)"} true;
L4:

    // $t19 := 0 at ../../../../swap/src/modules/module.move:21:25+1
    $t19 := 0;
    assume $IsValid'u64'($t19);

    // trace_local[j]($t19) at ../../../../swap/src/modules/module.move:21:21+1
    assume {:print "$track_local(1,0,2):", $t19} $t19 == $t19;

    // label L14 at ../../../../swap/src/modules/module.move:23:21+471
    assume {:print "$at(9,686,1157)"} true;
L14:

    // assert Eq<num>(Len<u64>($t0), Len<u64>($t7)) at ../../../../swap/src/modules/module.move:24:25+32
    assume {:print "$at(9,716,748)"} true;
    assert {:msg "assert_failed(9,716,748): base case of the loop invariant does not hold"}
      $IsEqual'num'(LenVec($Dereference($t0)), LenVec($t7));

    // assert Le($t19, Sub(Sub($t12, $t10), 1)) at ../../../../swap/src/modules/module.move:25:25+21
    assume {:print "$at(9,773,794)"} true;
    assert {:msg "assert_failed(9,773,794): base case of the loop invariant does not hold"}
      ($t19 <= (($t12 - $t10) - 1));

    // assert forall k: Range(0, $t19): Le(Index($t0, k), Index($t0, $t19)) at ../../../../swap/src/modules/module.move:26:25+41
    assume {:print "$at(9,819,860)"} true;
    assert {:msg "assert_failed(9,819,860): base case of the loop invariant does not hold"}
      (var $range_0 := $Range(0, $t19); (forall $i_1: int :: $InRange($range_0, $i_1) ==> (var k := $i_1;
    ((ReadVec($Dereference($t0), k) <= ReadVec($Dereference($t0), $t19))))));

    // assert forall p: Range(0, Sub($t12, $t10)), q: Range(Sub($t12, $t10), $t12): Le(Index($t0, p), Index($t0, q)) at ../../../../swap/src/modules/module.move:28:25+56
    assume {:print "$at(9,987,1043)"} true;
    assert {:msg "assert_failed(9,987,1043): base case of the loop invariant does not hold"}
      (var $range_0 := $Range(0, ($t12 - $t10)); (var $range_1 := $Range(($t12 - $t10), $t12); (forall $i_2: int, $i_3: int :: $InRange($range_0, $i_2) ==> $InRange($range_1, $i_3) ==> (var p := $i_2;
    (var q := $i_3;
    ((ReadVec($Dereference($t0), p) <= ReadVec($Dereference($t0), q))))))));

    // assert forall m: Range(Sub($t12, $t10), $t12), n: Range(Sub($t12, $t10), $t12): Implies(Le(m, n), Le(Index($t0, m), Index($t0, n))) at ../../../../swap/src/modules/module.move:29:25+67
    assume {:print "$at(9,1068,1135)"} true;
    assert {:msg "assert_failed(9,1068,1135): base case of the loop invariant does not hold"}
      (var $range_0 := $Range(($t12 - $t10), $t12); (var $range_1 := $Range(($t12 - $t10), $t12); (forall $i_2: int, $i_3: int :: $InRange($range_0, $i_2) ==> $InRange($range_1, $i_3) ==> (var m := $i_2;
    (var n := $i_3;
    (((m <= n) ==> (ReadVec($Dereference($t0), m) <= ReadVec($Dereference($t0), n)))))))));

    // havoc[val]($t19) at ../../../../swap/src/modules/module.move:29:25+67
    havoc $t19;
    assume $IsValid'u64'($t19);

    // havoc[val]($t20) at ../../../../swap/src/modules/module.move:29:25+67
    havoc $t20;
    assume $IsValid'u64'($t20);

    // havoc[val]($t21) at ../../../../swap/src/modules/module.move:29:25+67
    havoc $t21;
    assume $IsValid'u64'($t21);

    // havoc[val]($t22) at ../../../../swap/src/modules/module.move:29:25+67
    havoc $t22;
    assume $IsValid'u64'($t22);

    // havoc[val]($t23) at ../../../../swap/src/modules/module.move:29:25+67
    havoc $t23;
    assume $IsValid'bool'($t23);

    // havoc[val]($t24) at ../../../../swap/src/modules/module.move:29:25+67
    havoc $t24;
    assume $IsValid'u64'($t24);

    // havoc[val]($t25) at ../../../../swap/src/modules/module.move:29:25+67
    havoc $t25;
    assume $IsValid'u64'($t25);

    // havoc[val]($t26) at ../../../../swap/src/modules/module.move:29:25+67
    havoc $t26;
    assume $IsValid'u64'($t26);

    // havoc[val]($t27) at ../../../../swap/src/modules/module.move:29:25+67
    havoc $t27;
    assume $IsValid'u64'($t27);

    // havoc[val]($t28) at ../../../../swap/src/modules/module.move:29:25+67
    havoc $t28;
    assume $IsValid'bool'($t28);

    // havoc[val]($t29) at ../../../../swap/src/modules/module.move:29:25+67
    havoc $t29;
    assume $IsValid'u64'($t29);

    // havoc[val]($t30) at ../../../../swap/src/modules/module.move:29:25+67
    havoc $t30;
    assume $IsValid'u64'($t30);

    // havoc[val]($t31) at ../../../../swap/src/modules/module.move:29:25+67
    havoc $t31;
    assume $IsValid'u64'($t31);

    // havoc[val]($t32) at ../../../../swap/src/modules/module.move:29:25+67
    havoc $t32;
    assume $IsValid'u64'($t32);

    // havoc[mut]($t0) at ../../../../swap/src/modules/module.move:29:25+67
    havoc $temp_0'vec'u64'';
    $t0 := $UpdateMutation($t0, $temp_0'vec'u64'');
    assume $IsValid'vec'u64''($Dereference($t0));

    // havoc[mut_all]($t35) at ../../../../swap/src/modules/module.move:29:25+67
    havoc $t35;
    assume $IsValid'u64'($Dereference($t35));

    // havoc[mut_all]($t36) at ../../../../swap/src/modules/module.move:29:25+67
    havoc $t36;
    assume $IsValid'u64'($Dereference($t36));

    // assume Not(AbortFlag()) at ../../../../swap/src/modules/module.move:29:25+67
    assume !$abort_flag;

    // assume Eq<num>(Len<u64>($t0), Len<u64>($t5)) at ../../../../swap/src/modules/module.move:24:25+32
    assume {:print "$at(9,716,748)"} true;
    assume $IsEqual'num'(LenVec($Dereference($t0)), LenVec($t5));

    // assume Le($t19, Sub(Sub($t12, $t10), 1)) at ../../../../swap/src/modules/module.move:25:25+21
    assume {:print "$at(9,773,794)"} true;
    assume ($t19 <= (($t12 - $t10) - 1));

    // assume forall k: Range(0, $t19): Le(Index($t0, k), Index($t0, $t19)) at ../../../../swap/src/modules/module.move:26:25+41
    assume {:print "$at(9,819,860)"} true;
    assume (var $range_0 := $Range(0, $t19); (forall $i_1: int :: $InRange($range_0, $i_1) ==> (var k := $i_1;
    ((ReadVec($Dereference($t0), k) <= ReadVec($Dereference($t0), $t19))))));

    // assume forall p: Range(0, Sub($t12, $t10)), q: Range(Sub($t12, $t10), $t12): Le(Index($t0, p), Index($t0, q)) at ../../../../swap/src/modules/module.move:28:25+56
    assume {:print "$at(9,987,1043)"} true;
    assume (var $range_0 := $Range(0, ($t12 - $t10)); (var $range_1 := $Range(($t12 - $t10), $t12); (forall $i_2: int, $i_3: int :: $InRange($range_0, $i_2) ==> $InRange($range_1, $i_3) ==> (var p := $i_2;
    (var q := $i_3;
    ((ReadVec($Dereference($t0), p) <= ReadVec($Dereference($t0), q))))))));

    // assume forall m: Range(Sub($t12, $t10), $t12), n: Range(Sub($t12, $t10), $t12): Implies(Le(m, n), Le(Index($t0, m), Index($t0, n))) at ../../../../swap/src/modules/module.move:29:25+67
    assume {:print "$at(9,1068,1135)"} true;
    assume (var $range_0 := $Range(($t12 - $t10), $t12); (var $range_1 := $Range(($t12 - $t10), $t12); (forall $i_2: int, $i_3: int :: $InRange($range_0, $i_2) ==> $InRange($range_1, $i_3) ==> (var m := $i_2;
    (var n := $i_3;
    (((m <= n) ==> (ReadVec($Dereference($t0), m) <= ReadVec($Dereference($t0), n)))))))));

    // $t20 := +($t12, $t10) on_abort goto L18 with $t13 at ../../../../swap/src/modules/module.move:31:27+1
    assume {:print "$at(9,1185,1186)"} true;
    call $t20 := $AddU64($t12, $t10);
    if ($abort_flag) {
        assume {:print "$at(9,1185,1186)"} true;
        $t13 := $abort_code;
        assume {:print "$track_abort(1,0):", $t13} $t13 == $t13;
        goto L18;
    }

    // $t21 := 1 at ../../../../swap/src/modules/module.move:31:30+1
    $t21 := 1;
    assume $IsValid'u64'($t21);

    // $t22 := +($t20, $t21) on_abort goto L18 with $t13 at ../../../../swap/src/modules/module.move:31:29+1
    call $t22 := $AddU64($t20, $t21);
    if ($abort_flag) {
        assume {:print "$at(9,1187,1188)"} true;
        $t13 := $abort_code;
        assume {:print "$track_abort(1,0):", $t13} $t13 == $t13;
        goto L18;
    }

    // $t23 := <($t19, $t22) at ../../../../swap/src/modules/module.move:31:24+1
    call $t23 := $Lt($t19, $t22);

    // if ($t23) goto L7 else goto L8 at ../../../../swap/src/modules/module.move:22:17+730
    assume {:print "$at(9,658,1388)"} true;
    if ($t23) { goto L7; } else { goto L8; }

    // label L8 at ../../../../swap/src/modules/module.move:22:17+730
L8:

    // goto L9 at ../../../../swap/src/modules/module.move:22:17+730
    goto L9;

    // label L7 at ../../../../swap/src/modules/module.move:33:45+1
    assume {:print "$at(9,1256,1257)"} true;
L7:

    // $t35 := Vector::borrow_mut<u64>($t0, $t19) on_abort goto L18 with $t13 at ../../../../swap/src/modules/module.move:33:26+23
    call $t35,$t0 := $1_Vector_borrow_mut'u64'($t0, $t19);
    if ($abort_flag) {
        assume {:print "$at(9,1237,1260)"} true;
        $t13 := $abort_code;
        assume {:print "$track_abort(1,0):", $t13} $t13 == $t13;
        goto L18;
    }

    // $t24 := read_ref($t35) at ../../../../swap/src/modules/module.move:33:25+24
    $t24 := $Dereference($t35);

    // $t25 := 1 at ../../../../swap/src/modules/module.move:33:76+1
    $t25 := 1;
    assume $IsValid'u64'($t25);

    // $t26 := -($t19, $t25) on_abort goto L18 with $t13 at ../../../../swap/src/modules/module.move:33:75+1
    call $t26 := $Sub($t19, $t25);
    if ($abort_flag) {
        assume {:print "$at(9,1286,1287)"} true;
        $t13 := $abort_code;
        assume {:print "$track_abort(1,0):", $t13} $t13 == $t13;
        goto L18;
    }

    // $t36 := Vector::borrow_mut<u64>($t0, $t26) on_abort goto L18 with $t13 at ../../../../swap/src/modules/module.move:33:53+25
    call $t36,$t0 := $1_Vector_borrow_mut'u64'($t0, $t26);
    if ($abort_flag) {
        assume {:print "$at(9,1264,1289)"} true;
        $t13 := $abort_code;
        assume {:print "$track_abort(1,0):", $t13} $t13 == $t13;
        goto L18;
    }

    // $t27 := read_ref($t36) at ../../../../swap/src/modules/module.move:33:52+26
    $t27 := $Dereference($t36);

    // $t28 := >($t24, $t27) at ../../../../swap/src/modules/module.move:33:50+1
    call $t28 := $Gt($t24, $t27);

    // if ($t28) goto L10 else goto L11 at ../../../../swap/src/modules/module.move:33:21+107
    if ($t28) { goto L10; } else { goto L11; }

    // label L11 at ../../../../swap/src/modules/module.move:33:21+107
L11:

    // goto L12 at ../../../../swap/src/modules/module.move:33:21+107
    goto L12;

    // label L10 at ../../../../swap/src/modules/module.move:33:21+107
L10:

    // goto L13 at ../../../../swap/src/modules/module.move:33:21+107
    goto L13;

    // label L12 at ../../../../swap/src/modules/module.move:34:38+1
    assume {:print "$at(9,1329,1330)"} true;
L12:

    // $t29 := 1 at ../../../../swap/src/modules/module.move:34:44+1
    $t29 := 1;
    assume $IsValid'u64'($t29);

    // $t30 := -($t19, $t29) on_abort goto L18 with $t13 at ../../../../swap/src/modules/module.move:34:43+1
    call $t30 := $Sub($t19, $t29);
    if ($abort_flag) {
        assume {:print "$at(9,1334,1335)"} true;
        $t13 := $abort_code;
        assume {:print "$track_abort(1,0):", $t13} $t13 == $t13;
        goto L18;
    }

    // Vector::swap<u64>($t0, $t19, $t30) on_abort goto L18 with $t13 at ../../../../swap/src/modules/module.move:34:25+21
    call $t0 := $1_Vector_swap'u64'($t0, $t19, $t30);
    if ($abort_flag) {
        assume {:print "$at(9,1316,1337)"} true;
        $t13 := $abort_code;
        assume {:print "$track_abort(1,0):", $t13} $t13 == $t13;
        goto L18;
    }

    // label L13 at ../../../../swap/src/modules/module.move:35:25+1
    assume {:print "$at(9,1365,1366)"} true;
L13:

    // $t31 := 1 at ../../../../swap/src/modules/module.move:35:28+1
    $t31 := 1;
    assume $IsValid'u64'($t31);

    // $t32 := -($t19, $t31) on_abort goto L18 with $t13 at ../../../../swap/src/modules/module.move:35:27+1
    call $t32 := $Sub($t19, $t31);
    if ($abort_flag) {
        assume {:print "$at(9,1367,1368)"} true;
        $t13 := $abort_code;
        assume {:print "$track_abort(1,0):", $t13} $t13 == $t13;
        goto L18;
    }

    // trace_local[j]($t32) at ../../../../swap/src/modules/module.move:35:21+1
    assume {:print "$track_local(1,0,2):", $t32} $t32 == $t32;

    // goto L16 at ../../../../swap/src/modules/module.move:35:29+1
    goto L16;

    // label L9 at ../../../../swap/src/modules/module.move:37:21+1
    assume {:print "$at(9,1410,1411)"} true;
L9:

    // $t33 := 1 at ../../../../swap/src/modules/module.move:37:25+1
    $t33 := 1;
    assume $IsValid'u64'($t33);

    // $t34 := -($t10, $t33) on_abort goto L18 with $t13 at ../../../../swap/src/modules/module.move:37:23+1
    call $t34 := $Sub($t10, $t33);
    if ($abort_flag) {
        assume {:print "$at(9,1412,1413)"} true;
        $t13 := $abort_code;
        assume {:print "$track_abort(1,0):", $t13} $t13 == $t13;
        goto L18;
    }

    // trace_local[i]($t34) at ../../../../swap/src/modules/module.move:37:17+1
    assume {:print "$track_local(1,0,1):", $t34} $t34 == $t34;

    // goto L15 at ../../../../swap/src/modules/module.move:37:26+1
    goto L15;

    // label L6 at ../../../../swap/src/modules/module.move:8:9+1295
    assume {:print "$at(9,145,1440)"} true;
L6:

    // destroy($t0) at ../../../../swap/src/modules/module.move:8:9+1295

    // label L3 at ../../../../swap/src/modules/module.move:8:9+1295
L3:

    // trace_local[v]($t0) at ../../../../swap/src/modules/module.move:8:9+1295
    $temp_0'vec'u64'' := $Dereference($t0);
    assume {:print "$track_local(1,0,0):", $temp_0'vec'u64''} $temp_0'vec'u64'' == $temp_0'vec'u64'';

    // goto L17 at ../../../../swap/src/modules/module.move:8:9+1295
    goto L17;

    // label L15 at ../../../../swap/src/modules/module.move:8:9+1295
    // Loop invariant checking block for the loop started with header: L2
L15:

    // assert Eq<num>(Len<u64>($t0), Len<u64>($t8)) at ../../../../swap/src/modules/module.move:11:21+32
    assume {:print "$at(9,221,253)"} true;
    assert {:msg "assert_failed(9,221,253): induction case of the loop invariant does not hold"}
      $IsEqual'num'(LenVec($Dereference($t0)), LenVec($t8));

    // assert Le($t34, Len<u64>($t0)) at ../../../../swap/src/modules/module.move:12:21+22
    assume {:print "$at(9,274,296)"} true;
    assert {:msg "assert_failed(9,274,296): induction case of the loop invariant does not hold"}
      ($t34 <= LenVec($Dereference($t0)));

    // assert forall p: Range(0, Sub($t12, $t34)), q: Range(Sub($t12, $t34), $t12): Le(Index($t0, p), Index($t0, q)) at ../../../../swap/src/modules/module.move:13:21+56
    assume {:print "$at(9,317,373)"} true;
    assert {:msg "assert_failed(9,317,373): induction case of the loop invariant does not hold"}
      (var $range_0 := $Range(0, ($t12 - $t34)); (var $range_1 := $Range(($t12 - $t34), $t12); (forall $i_2: int, $i_3: int :: $InRange($range_0, $i_2) ==> $InRange($range_1, $i_3) ==> (var p := $i_2;
    (var q := $i_3;
    ((ReadVec($Dereference($t0), p) <= ReadVec($Dereference($t0), q))))))));

    // assert forall m: Range(Sub($t12, $t34), $t12), n: Range(Sub($t12, $t34), $t12): Implies(Le(m, n), Le(Index($t0, m), Index($t0, n))) at ../../../../swap/src/modules/module.move:14:21+67
    assume {:print "$at(9,394,461)"} true;
    assert {:msg "assert_failed(9,394,461): induction case of the loop invariant does not hold"}
      (var $range_0 := $Range(($t12 - $t34), $t12); (var $range_1 := $Range(($t12 - $t34), $t12); (forall $i_2: int, $i_3: int :: $InRange($range_0, $i_2) ==> $InRange($range_1, $i_3) ==> (var m := $i_2;
    (var n := $i_3;
    (((m <= n) ==> (ReadVec($Dereference($t0), m) <= ReadVec($Dereference($t0), n)))))))));

    // stop() at ../../../../swap/src/modules/module.move:14:21+67
    assume false;
    return;

    // label L16 at ../../../../swap/src/modules/module.move:14:21+67
    // Loop invariant checking block for the loop started with header: L14
L16:

    // assert Eq<num>(Len<u64>($t0), Len<u64>($t9)) at ../../../../swap/src/modules/module.move:24:25+32
    assume {:print "$at(9,716,748)"} true;
    assert {:msg "assert_failed(9,716,748): induction case of the loop invariant does not hold"}
      $IsEqual'num'(LenVec($Dereference($t0)), LenVec($t9));

    // assert Le($t32, Sub(Sub($t12, $t10), 1)) at ../../../../swap/src/modules/module.move:25:25+21
    assume {:print "$at(9,773,794)"} true;
    assert {:msg "assert_failed(9,773,794): induction case of the loop invariant does not hold"}
      ($t32 <= (($t12 - $t10) - 1));

    // assert forall k: Range(0, $t32): Le(Index($t0, k), Index($t0, $t32)) at ../../../../swap/src/modules/module.move:26:25+41
    assume {:print "$at(9,819,860)"} true;
    assert {:msg "assert_failed(9,819,860): induction case of the loop invariant does not hold"}
      (var $range_0 := $Range(0, $t32); (forall $i_1: int :: $InRange($range_0, $i_1) ==> (var k := $i_1;
    ((ReadVec($Dereference($t0), k) <= ReadVec($Dereference($t0), $t32))))));

    // assert forall p: Range(0, Sub($t12, $t10)), q: Range(Sub($t12, $t10), $t12): Le(Index($t0, p), Index($t0, q)) at ../../../../swap/src/modules/module.move:28:25+56
    assume {:print "$at(9,987,1043)"} true;
    assert {:msg "assert_failed(9,987,1043): induction case of the loop invariant does not hold"}
      (var $range_0 := $Range(0, ($t12 - $t10)); (var $range_1 := $Range(($t12 - $t10), $t12); (forall $i_2: int, $i_3: int :: $InRange($range_0, $i_2) ==> $InRange($range_1, $i_3) ==> (var p := $i_2;
    (var q := $i_3;
    ((ReadVec($Dereference($t0), p) <= ReadVec($Dereference($t0), q))))))));

    // assert forall m: Range(Sub($t12, $t10), $t12), n: Range(Sub($t12, $t10), $t12): Implies(Le(m, n), Le(Index($t0, m), Index($t0, n))) at ../../../../swap/src/modules/module.move:29:25+67
    assume {:print "$at(9,1068,1135)"} true;
    assert {:msg "assert_failed(9,1068,1135): induction case of the loop invariant does not hold"}
      (var $range_0 := $Range(($t12 - $t10), $t12); (var $range_1 := $Range(($t12 - $t10), $t12); (forall $i_2: int, $i_3: int :: $InRange($range_0, $i_2) ==> $InRange($range_1, $i_3) ==> (var m := $i_2;
    (var n := $i_3;
    (((m <= n) ==> (ReadVec($Dereference($t0), m) <= ReadVec($Dereference($t0), n)))))))));

    // stop() at ../../../../swap/src/modules/module.move:29:25+67
    assume false;
    return;

    // label L17 at ../../../../swap/src/modules/module.move:40:5+1
    assume {:print "$at(9,1445,1446)"} true;
L17:

    // assert forall i: Range(0, Len<u64>($t0)), j: Range(0, Len<u64>($t0)): Implies(Le(i, j), Le(Index($t0, i), Index($t0, j))) at ../../../../swap/src/modules/module.move:43:9+71
    assume {:print "$at(9,1487,1558)"} true;
    assert {:msg "assert_failed(9,1487,1558): post-condition does not hold"}
      (var $range_0 := $Range(0, LenVec($Dereference($t0))); (var $range_1 := $Range(0, LenVec($Dereference($t0))); (forall $i_2: int, $i_3: int :: $InRange($range_0, $i_2) ==> $InRange($range_1, $i_3) ==> (var i := $i_2;
    (var j := $i_3;
    (((i <= j) ==> (ReadVec($Dereference($t0), i) <= ReadVec($Dereference($t0), j)))))))));

    // return () at ../../../../swap/src/modules/module.move:43:9+71
    $ret0 := $t0;
    return;

    // label L18 at ../../../../swap/src/modules/module.move:40:5+1
    assume {:print "$at(9,1445,1446)"} true;
L18:

    // abort($t13) at ../../../../swap/src/modules/module.move:40:5+1
    $abort_code := $t13;
    $abort_flag := true;
    return;

    // label L19 at <internal>:1:1+10
    assume {:print "$at(1,0,10)"} true;
L19:

    // destroy($t35) at <internal>:1:1+10

    // destroy($t36) at <internal>:1:1+10

    // goto L0 at <internal>:1:1+10
    goto L0;

    // label L20 at <internal>:1:1+10
L20:

    // destroy($t35) at <internal>:1:1+10

    // destroy($t36) at <internal>:1:1+10

    // goto L5 at <internal>:1:1+10
    goto L5;

}
