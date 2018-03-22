//@ #include "vfarray.gh"
//@ #include "multiset.gh"

/*@
fixpoint int card(int x, list<pair<int,int> > xs){
    switch (xs) {
        case nil: return 0;
        case cons(x0,xs0) : return (snd(x0) == x ? 1 : 0) + card(x,xs0);
    }
}

fixpoint list<int> list_elem(list<pair<int,int> > xs) {
    switch (xs) {
        case nil: return nil;
        case cons(x0,xs0): return mem(snd(x0),list_elem(xs0)) ? list_elem(xs0) : cons(snd(x0),list_elem(xs0));
    }
}

fixpoint list<pair<int,int> > list_card(list<int> xs,list<pair<int,int> > l) {
    switch (xs) {
    	case nil : return nil;
    	case cons(x0,xs0): return cons(pair(x0,card(x0,l)),list_card(xs0,l));
    }
}

predicate array_to_list(array(int,int) m,int b,int e;list<pair<int,int> > xs) =
    (b >= e) ? 
    xs == nil :
    (array_to_list(m, b+1, e, ?tl) &*&
    	xs == cons(pair(b, get(m,b)),tl));

predicate same_card(pair<int,int> x, list<pair<int,int> > xs) =
    xs == nil ?
    false :
    xs == cons(?x0, ?xs0) &*& (fst(x) == fst(x0) ? snd(x) == snd(x0) : same_card(x, xs0));

predicate all_same_card(list<pair<int,int> > ref, list<pair<int,int> > end) =
    ref == nil ?	
    true : 
    ref == cons(?x,?ref0) &*& same_card(x,end) &*& all_same_card (ref0,end); 

predicate same_multiset(array(int,int) start, array(int,int) end,int b, int e) =
  array_to_list(start, b, e, ?m) &*& array_to_list(end, b, e, ?m') &*&
  all_same_card(list_card(list_elem(m),m),list_card(list_elem(m'),m'));

lemma void same_multiset_refl (array(int,int) start, int b, int e)
  requires true;
  ensures same_multiset(start, start, b, e);
{assume(false);}

fixpoint array(int, int) array_swap(array(int, int) start, int i, int j) {
  return set(set(start, j, get(start, i)), i, get(start, j));
}

lemma void same_multiset_swap(array(int, int) start, int i, int j, int b, int e)
  requires true;
  ensures same_multiset(start, array_swap(start, i, j), b, e);
{ assume(false); }

lemma void same_multiset_trans(array(int, int) start, array(int, int) middle, array(int, int) end, int b, int e)
  requires same_multiset(start, middle, b, e) &*& same_multiset(middle, end, b, e);
  ensures same_multiset(start, end, b, e);
{ assume(false); }

lemma void swap_out(array(int, int) arr, int i, int j, int k)
  requires k != i &*& k != j;
  ensures get(array_swap(arr, i, j), k) == get(arr, k);
{ assume(false); }

lemma void swap_in_i(array(int, int) arr, int i, int j)
  requires true;
  ensures get(array_swap(arr, i, j), i) == get(arr, j);
{ assume(false); }

lemma void swap_in_j(array(int, int) arr, int i, int j)
  requires true;
  ensures get(array_swap(arr, i, j), j) == get(arr, i);
{ assume(false); }

lemma void same_multiset_add_at_end(array(int, int) start, array(int, int) end, int b, int e)
  requires same_multiset(start, end, b, e) &*& get(start, e) == get(end, e);
  ensures same_multiset(start, end, b, e+1);
{ assume(false); }

@*/
void swap (int* a, int i, int j)
//@ requires array_model(a, ?b, ?e, ?start) &*& b <= i &*& i < j &*& j < e;
//@ ensures array_model(a, b, e, array_swap(start, i, j));
{
  //@ array_model_get_unfold(a, b, e, start, i);
  //@ array_model_get_unfold(a, i+1, e, start, j);
  int h = *(a+i);
  a[i] = *(a+j);
  a[j] = h;
  //@ array_model_set_fold(a, i+1, e, start, j);
  //@ array_model_out_of_range(a, b, i, start, j, get(start, i));
  //@ array_model_set_fold(a, b, e, set(start, j, get(start, i)), i);
}

//@ predicate minore(int* arr, int lo, int hi, int bound);
//@ predicate majore(int* arr, int lo, int hi, int bound);

  
/*@lemma int need(int i,int b,int lo) 
    requires b <= lo &*& lo - 1 <= i ;
    ensures b <= i+1 &*& i +1 ==result +1;
    {
    	int j =i;
    	return j;
    }

@*/
int partition (int* a, int lo, int hi)
//@ requires array_model(a, lo, hi, ?start) &*& lo < hi &*& pointsto(a+hi,?p) &*& p == get(start, hi);
/*@ ensures array_model(a, lo, hi+1, ?end) &*& same_multiset(start, end, lo, hi+1) &*&
      lo <= result &*& result <= hi &*&
      //minore(a, lo, result-1, p) &*&
      //majore(a, result+1, hi, p) &*&
      get(end, result) == p; @*/
{
  int pivot = *(a+hi);
  int i = lo - 1;
  int j;
  //@ same_multiset_refl(start, lo, hi);
  for (j = lo; j < hi; j++) 
  //@ invariant array_model(a,lo,hi,?arr) &*& lo <= j &*& j < hi+1 &*& i < j &*& lo -1 <= i &*& same_multiset(start, arr, lo, hi) &*& get(arr, hi) == p;
  { 
    //@ assert (j < hi);
    //@ array_model_get_unfold(a,lo,hi,arr,j);
    if (*(a+j) < pivot) {
      i++;
      //@ array_model_get_fold(a,lo,hi,arr,j);
      if (i < j) {
        swap(a, i, j);
        //@ same_multiset_swap(arr, i, j, lo, hi);
        //@ same_multiset_trans(start, arr, array_swap(arr, i, j), lo, hi);
        //@ swap_out(arr, i, j, hi);
      }
    }
    //@ if (get(arr, j) >= pivot) array_model_get_fold(a, lo, hi, arr, j);
  }
  //@ assert array_model(a, lo, hi, ?arr);
  i++;
  //@ empty_array(a, hi+1, arr);
  //@ array_model_get_fold(a, lo, hi+1, arr, hi);
  //@ same_multiset_add_at_end(start, arr, lo, hi);
  if (i < hi) {
    swap(a, i, hi);
    //@ same_multiset_swap(arr, i, hi, lo, hi+1);
    //@ same_multiset_trans(start, arr, array_swap(arr, i, hi), lo, hi+1);
    //@ swap_in_i(arr, i, hi);
  }
  return i;
}

//@ predicate sorted(array(int,int) arr);

void quicksort (int* a, int lo, int hi)
//@ requires array_model(a, ?b, ?e, ?start) &*& b <= lo &*& hi < e;
//@ ensures array_model(a, lo, hi, ?end) &*& same_multiset(start, end,b,e) &*& sorted(end);
{
  if (lo >= hi) return;
  int p = partition(a, lo, hi);
  quicksort(a, lo, p-1);
  quicksort(a, p+1, hi);
}
