address 0x2{
module Test{
    use Std::Vector;

    fun sort(v: &mut vector<u64>){
        let i = 0;
        let l = Vector::length(v);
        if (l != 0) {
            while({
                spec{
                    invariant len(v) == len(old(v));
                    invariant i <= len(v);
                    invariant forall p in 0..l-i, q in l-i..l: v[p] <= v[q];
                    invariant forall m in l-i..l, n in l-i..l: m <= n ==> v[m] <= v[n];
                    //invariant (i != l-1) ==> (forall m in 0..i: v[l-m-1] >= v[l-m-2]);

                };
                (i < l-1)

            }) {
                let j = 0;
                while({
                    spec{
                        invariant len(v) == len(old(v));
                        invariant j <= l-i-1;
                        invariant forall k in 0..j: v[k] <= v[j];
                        //invariant (i != l-1 && i >=1) ==>(forall m in 0..i-1: v[l-m-1] >=v[l-m-2]);
                        invariant forall p in 0..l-i, q in l-i..l: v[p] <= v[q];
                        invariant forall m in l-i..l, n in l-i..l: m <= n ==> v[m] <= v[n];
                    };
                    (j < l-i-1)
                }) {
                    if (*Vector::borrow_mut(v,j) > *Vector::borrow_mut(v,j+1)){
                        Vector::swap(v,j,j+1);};
                    j = j +1;
                };
                i = i + 1;
            }
        }
    }
    spec sort{
        //sorted
        ensures forall i in 0..len(v), j in 0..len(v): i <= j ==> v[i] <= v[j];

    }
}
}