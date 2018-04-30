//@ #include "vfarray2.gh"

//@ #include "multiset2.gh"

/*@

lemma void same_multiset_refl (array(int,int) start, int b, int e)
  requires true;
  ensures same_multiset(start, start, b, e);
{
   if (b >= e) {
     close array_multiset(b, e, start, empty_multiset());
     close array_multiset(b, e, start, empty_multiset());
     close same_multiset(start, start, b, e);
   } else {
     int i = e;
     close array_multiset(i, e, start, empty_multiset());
     close array_multiset(i, e, start, empty_multiset());
     close same_multiset(start, start, i, e);
     for (; i > b; i--)
       invariant b <= i &*& i <= e &*& same_multiset(start, start, i, e);
       decreases (i-b);
       {
          open same_multiset(start, start, i, e);
          assert array_multiset(i, e, start, ?tl);
          close array_multiset(i-1, e, start, multiset_add(tl, get(start, i-1)));
          close array_multiset(i-1, e, start, multiset_add(tl, get(start, i-1)));
          close same_multiset(start, start, i-1, e);
       }
   }
}

/*
lemma void int_compare_model(int b, int e)
  requires array_model(?a, b, e, ?arr);
  ensures array_model(a, b, e, arr) &*& int_compare(b, e);
{
  if(b >= e) {
    close int_compare(b, e);
  } else {
    open array_model(a, b, e, arr);
    open array_forall(a, b, e, ?p);
    open array_list_model<int, int>(a, b, e, int_pto, _);
    close array_forall(a, b+1, e, p);
    close array_model(a, b+1, e, arr);
    open int_pto(a, b, _);
    assert a[b] |-> ?hd;
    assert integer(a+b, hd);
    open integer(a+b, hd);
    int_compare_model(b+1, e);
    close array_model(a, b, e, arr);
    close int_compare(b, e);
  }
}  
*/

fixpoint array(int, int) array_swap(array(int, int) start, int i, int j) {
  return set(set(start, j, get(start, i)), i, get(start, j));
}


  

lemma void same_multiset_swap(array(int, int) start, int i, int j, int b, int e)
  requires b <= i &*& i < j &*& j < e;
  ensures same_multiset(start, array_swap(start, i, j), b, e);
{  array(int, int) end = array_swap(start, i, j);
   if (b >= e) {
     close array_multiset(b, e, start, empty_multiset());
     close array_multiset(b, e, end, empty_multiset());
     close same_multiset(start, end, b, e);
  }else{
     int k = e;
     close array_multiset(k, e, start, empty_multiset());
     close array_multiset(k, e, end, empty_multiset());
     for(; k > j+1; k--)
     invariant j < k &*& k <= e &*& array_multiset(k, e, start, ?MA) &*& array_multiset(k, e, end, ?MB) &*& MA == MB;
     decreases (k-j);
     {
       close array_multiset(k-1, e, start, multiset_add (MA, get(start, k-1)));
       // next line uses the theory of array
       assert (get(start,k-1) == get(end, k-1));
       close array_multiset(k-1, e, end, multiset_add (MB, get(start, k-1)));
     }
     assert array_multiset(k, e, start, ?MA) &*& array_multiset(k, e, end, ?MB);
     close array_multiset(j, e, start, multiset_add(MA, get(start,j)));
     // next line uses the theory of array
     assert (get(start,i) == get(end, j));
     close array_multiset(j, e, end, multiset_add(MB, get(start,i)));
     k--;
     multiset_add_commutes(MA, get(start, i), get(start, j));
     for(; k > i+1; k--)
     invariant i < k &*& k <= j &*& array_multiset(k, e, start, ?MA2) &*& array_multiset(k, e, end, ?MB2) &*& multiset_add(MA2, get(start,i)) == multiset_add(MB2, get(start,j));
     decreases (k-i);
     {
     	close array_multiset(k-1, e, start, multiset_add(MA2, get(start,k-1)));
     	assert (get(start,k-1) == get(end, k-1));
        close array_multiset(k-1, e, end, multiset_add (MB2, get(start,k-1)));
        multiset_add_commutes(MA2, get(start, i), get(start, k-1));
        multiset_add_commutes(MB2, get(start, j), get(start, k-1));
     }  
     assert array_multiset(k, e, start, ?MA2) &*& array_multiset(k, e, end, ?MB2);  
     close array_multiset(i, e, start, multiset_add(MA2, get(start,i)));
     close array_multiset(i, e, start, multiset_add(MB2, get(start,j)));
     k--;
     for(; k > b; k--)
     invariant b <= k &*& k <= i &*& array_multiset(k, e, start, ?MA3) &*& array_multiset(k, e, end, ?MB3) &*& MA3 == MB3;
     decreases (k-b);
     {
     	close array_multiset(k-1, e, start, multiset_add(MA3, get(start,k-1)));
     	assert (get(start,k-1) == get(end, k-1));
        close array_multiset(k-1, e, end, multiset_add(MB3, get(start,k-1)));
     } 
     close same_multiset(start, end, b, e);
     }
  }

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

int select(int* arr, int key)
//@ requires array_model(arr, ?lo, ?hi, ?m) &*& lo <= key &*& key < hi;
//@ ensures array_model(arr, lo, hi, m) &*& get(m, key) == result;
{
      //@ array_model_get_unfold(arr,lo,hi,m,key);
      int res = *(arr+key);
      //@ array_model_get_fold(arr,lo,hi,m,key);
      return res;
}

void update(int* arr, int key, int val)
//@ requires array_model(arr, ?lo, ?hi, ?m) &*& lo <= key &*& key < hi;
//@ ensures array_model(arr, lo, hi, set(m, key, val));
{
      //@ array_model_get_unfold(arr,lo,hi,m,key);
      *(arr+key) = val;
      //@ array_model_set_fold(arr,lo,hi,m,key);
}


void swap (int* a, int i, int j)
//@ requires array_model(a, ?b, ?e, ?start) &*& b <= i &*& i < j &*& j < e;
//@ ensures array_model(a, b, e, array_swap(start, i, j));
{
  int ai = select(a, i);
  int aj = select(a, j);
  update(a, j, ai);
  update(a, i, aj);
}

/*@ predicate minore(array(int,int) arr, int lo, int hi, int bound) =
	(lo>=hi) ? true :
	get(arr,lo) <= bound
	&*& minore(arr,lo+1,hi,bound);

    predicate majore(array(int,int) arr, int lo, int hi, int bound) = (lo>=hi) ? true : 
	get(arr,lo) >= bound &*& majore(arr,lo+1,hi,bound);

    lemma void bound_empty_minore(array(int,int) arr, int lo, int hi, int bound)
      requires lo >= hi;
      ensures minore(arr,lo,hi,bound);
      { assume(false);}
     
    lemma void bound_empty_majore(array(int,int) arr, int lo, int hi, int bound)
      requires lo >= hi;
      ensures majore(arr,lo,hi,bound);
      { assume(false);} 
     
    lemma void one_more_bot_bound_majore(array(int,int) arr, int lo, int hi, int bound, int i, int j)
    	requires majore(arr,lo,hi,bound) &*& i == lo &*& j == hi &*& get(arr,j) <= bound;
    	ensures majore(array_swap(arr,i,j),lo+1,hi+1,bound);
    	{ assume(false);}
     
     
    lemma void one_more_bound_minore(array(int,int) arr, int lo, int hi, int bound)
    	requires minore(arr,lo,hi,bound) &*& get(arr,hi) < bound;
    	ensures minore(arr,lo,hi+1,bound);
    	{ assume(false);}
    	
    lemma void one_more_bound_majore(array(int,int) arr, int lo, int hi, int bound)
    	requires majore(arr,lo,hi,bound) &*& get(arr,hi) >= bound;
    	ensures majore(arr,lo,hi+1,bound);
    	{ assume(false);}
    	
    lemma void equal_inf(int i,int j,int bound)
    	requires i == j &*& i < bound;
    	ensures j < bound;
    	{ assume(false);}
    	
    lemma void minore_out(array(int,int) arr,int lo, int hi, int bound, int i, int j)
    	requires minore(arr,lo,hi,bound) &*& hi <= i &*& hi <= j;
    	ensures minore(array_swap(arr,i,j),lo,hi,bound);
    	{ assume(false);}
    	
    lemma void majore_out(array(int,int) arr,int lo, int hi, int bound)
    	requires majore(arr,lo,hi,bound) &*& lo >= hi;
    	ensures majore(arr,lo+1,hi+1,bound);
    	{ assume(false);}
    	
    lemma void minore_less(array(int,int) arr,int lo, int hi, int bound)
    	requires minore(arr,lo,hi,bound);
    	ensures minore(arr,lo,hi-1,bound);
    	{ assume(false);}
    	
    lemma void majore_top_less(array(int,int) arr,int lo, int hi, int bound, int j)
    	requires majore(arr,lo,hi,bound) &*& j <= hi;
    	ensures majore(arr,lo,j,bound);
    	{ assume(false);}
    	
    lemma void majore_bot_less(array(int,int) arr,int lo, int hi, int bound)
    	requires majore(arr,lo,hi,bound);
    	ensures majore(arr,lo+1,hi,bound);
    	{ assume(false);}
    
    lemma void majore_top_more(array(int,int) arr,int lo,int hi,int bound)
    	requires majore(arr,lo,hi,bound) &*& get(arr,hi) >= bound;
    	ensures majore(arr,lo,hi+1,bound);
    	{assume(false);}
    	
    lemma void swap_majore(array(int,int) arr,int lo, int hi, int bound, int i, int j)
    	requires majore(arr,lo,hi,bound) &*& lo <= i &*& j < hi;
    	ensures majore(array_swap(arr,i,j),lo,hi,bound);
    	{ assume(false);}
@*/

int partition (int* a, int lo, int hi)
//@ requires array_model(a, lo, hi, ?start) &*& lo <= hi &*& pointsto(a+hi,?p) &*& p == get(start, hi);
/*@ ensures array_model(a, lo, hi+1, ?end) &*& same_multiset(start, end, lo, hi+1) &*&
      lo <= result &*& result <= hi &*&
      get(end, result) == p &*&
      minore(end, lo, result, get(end,result)) &*&
      majore(end, result+1, hi+1, get(end,result)); @*/
{
  int pivot = *(a+hi);
  int i = lo - 1;
  int j;
  //@ same_multiset_refl(start, lo, hi);
  //@ bound_empty_minore(start,lo,i+1,p);
  //@ bound_empty_majore(start,i+1,lo,p);
  for (j = lo; j < hi; j++) 
  /*@ invariant array_model(a,lo,hi,?arr) &*& lo <= j &*& j < hi+1 &*& i < j &*& lo -1 <= i &*& same_multiset(start, arr, lo, hi) &*& get(arr, hi) == p 
      &*& minore(arr,lo,i+1,p) &*& majore(arr,i+1,j,p); @*/
  { 
    // //@ assert (j < hi);
    int aj = select(a, j);
    if (aj < pivot) {
      i++;
      if (i < j) {
        swap(a, i, j);
        //@ same_multiset_swap(arr, i, j, lo, hi);
        //@ same_multiset_trans(start, arr, array_swap(arr, i, j), lo, hi);
        //@ swap_out(arr, i, j, hi);
        //@ swap_in_i(arr,i,j);
        //@ equal_inf(get(arr,j),get(array_swap(arr,i,j),i),p);
    	//@ minore_out(arr,lo, i, p, i, j);
      	//@ one_more_bound_minore(array_swap(arr,i,j),lo,i,p);
      	//@ one_more_bot_bound_majore(arr, i, j, p, i, j);
      }else{
      	//@ one_more_bound_minore(arr,lo,i,p);
      	//@ majore_out(arr, i, j, p);
      }
    }else{
   	//@ one_more_bound_majore(arr, i+1, j, p);
    }
    
  }
  //@ assert array_model(a, lo, hi, ?arr);
  //@ majore_top_less(arr, i+1, j, p, hi);
  //@ majore_top_more(arr, i+1, hi,p);
  i++;
  //@ empty_array(a, hi+1, arr);
 //@ array_model_get_fold(a, lo, hi+1, arr, hi);
 //@ same_multiset_add_at_end(start, arr, lo, hi);
  if (i < hi) {
    swap(a, i, hi);
  //@ same_multiset_swap(arr, i, hi, lo, hi+1);
  //@ same_multiset_trans(start, arr, array_swap(arr, i, hi), lo, hi+1);
  //@ swap_in_i(arr, i, hi);
  //@ minore_out(arr, lo, i, p, i, hi);
  ////@ minore_less(array_swap(arr,i,hi), lo, i, p);
  //@ swap_majore(arr, i, hi+1, p, i,hi);
  //@ majore_bot_less(array_swap(arr,i,hi), i, hi+1, p);
  }else{
  ////@ minore_less(arr, lo, i, p);
  //@ majore_bot_less(arr, i, hi+1, p);
  }
  return i;
}

/*@ predicate sorted(array(int,int) arr,int b, int e) =
     (b >= e) ? true : 
     get(arr,b) <= get(arr,b+1) &*& sorted(arr,b+1,e);
    
    lemma void empty_sorted(array(int,int)arr,int b, int e)
    	requires b>=e;
    	ensures sorted(arr,b,e);
    	{ assume(false);}
    	
    lemma void ensure_empty_array(int*a, int b,array(int,int) arr)
    	requires array_model(a,b,b,arr);
    	ensures true;
    	{assume(false);}
    	
    lemma void same_multi_etend(array(int,int) end, array(int,int) end1, int b, int e)
    	requires same_multiset(end,end1,b,e);
    	ensures same_multiset(end,set(end1,b-1,get(end,b-1)),b-1,e);
    	{assume(false);}
    	
    lemma void sorted_etend(array(int,int) end,int b, int e,int p,int v)
    	requires sorted(end,b,e) &*& p < b;
    	ensures sorted(set(end,p,v),b,e);
    	{assume(false);}
    	
    lemma void same_multi_ret(array(int,int) end, array(int,int) end1, int b, int e)
    	requires same_multiset(end,set(end1,b-1,get(end,b-1)),b-1,e);
    	ensures same_multiset(end,end1,b,e);
    	{assume(false);}
    	
    lemma void concat_array(int*a,array(int,int)a0,array(int,int)a1,int b0,int e0,int e1)
    	requires array_model(a,b0,e0,a0) &*& array_model(a,e0,e1,a1);// &*& same_multiset(res,a0,b0,e0) &*& same_multiset(res,a1,e0,e1);
    	ensures array_model(a,b0,e1,?res);// &*& same_multiset(res,?end,b0,e1);
    	{ assume(false);}
    	
    lemma void concat_array2(int*a, array(int,int)res, int b0, int e0, int e1)
    	requires array_model(a,b0,e0,res) &*& array_model(a,e0,e1,res);// &*& same_multiset(res,a0,b0,e0) &*& same_multiset(res,a1,b1,e1);
    	ensures array_model(a,b0,e1,res);// &*& same_multiset(res,?end,b0,e1);
    	{ assume(false);}
    	
    lemma void concat_array3(int*a, array(int,int) end, array(int,int) a0, array(int,int) a1, int b0, int e0, int e1, int bound)
    	requires array_model(a,b0,e0,a0) &*& array_model(a,e0,e1,a1) &*& same_multiset(end,a0,b0,e0) &*& same_multiset(end,a1,e0,e1) 
    		&*& sorted(a0,b0,e0) &*& sorted(a1,e0+1,e1) &*& minore(end,b0,e0,bound) &*& majore(end,e0+1,e1,bound) &*& bound == get(end,e0);
    	ensures array_model(a,b0,e1,?res) &*& same_multiset(res,end,b0,e1) &*& sorted(res,b0,e1);
    	{ assume(false);}
        
    lemma void concat_sorted(array(int,int)arr, array(int,int)arr0, array(int,int)arr1, int b0, int e0, int b1, int e1,int bound)
        requires same_multiset(arr,arr0,b0,e0) &*& same_multiset(arr,arr1,b1,e1) &*& sorted(arr0,b0,e0) &*& sorted(arr1,b1,e1) &*& minore(arr, b0, e0, bound) &*& majore(arr, b1, e1, bound) &*& e0 + 1 == b1 &*& bound == get(arr,e0);
        ensures sorted(arr,b0,e1);
        { assume(false);}
        
     lemma void concat_sorted2(array(int,int)arr, array(int,int)arr0, array(int,int)arr1, int b0, int e0, int b1, int e1,int bound)
        requires same_multiset(arr,arr0,b0,e0) &*& same_multiset(arr,arr1,b1,e1) &*& sorted(arr0,b0,e0) &*& sorted(arr1,b1,e1) &*& minore(arr, b0, e0, bound) &*& majore(arr, b1, e1, bound) &*& e0 + 1 == b1 &*& bound == get(arr,e0);
        ensures sorted(arr,b0,e1);
        { assume(false);}
                     
     lemma void multiset_trans(array(int,int) arr, array(int,int) arr0, array(int,int) arr1, int b, int e)
     	requires same_multiset(arr0,arr,b,e) &*& same_multiset(arr1,arr,b,e);
     	ensures same_multiset(arr0,arr1,b,e);
     	{assume(false);}
@*/
void quicksort (int* a, int lo, int hi)
//@ requires array_model(a, lo, hi+1, ?start);
//@ ensures array_model(a, lo, hi+1, ?end) &*& same_multiset(start, end,lo,hi+1) &*& sorted(end,lo,hi+1);
{
  if (lo > hi){
   //@ empty_sorted(start,lo,hi+1);
   //@ same_multiset_refl(start,lo,hi+1);
   return;
  }else{
   //@ array_model_get_unfold(a,lo,hi+1,start,hi);
   int p = partition(a, lo, hi);
   //@ assert array_model(a,lo,hi+1,?end);
   //@ array_model_get_unfold(a,lo,hi+1,end,p);
   quicksort(a, lo, p-1);
   //@ assert array_model(a,lo,p,?end0);
   quicksort(a, p+1, hi);
   //@ assert array_model(a,p+1,hi+1,?end1);
   //@ empty_array(a,p,end1);
   //@ array_model_set_fold(a,p,hi+1,end1,p);
   //@ ensure_empty_array(a,hi+1,start);
   ////@ concat_array(a,end0,set(end1,p,get(end,p)),lo,p,hi+1);
   ////@ concat_sorted(end, end0, end1, lo, p, p+1, hi+1, get(end,p));
   //@ same_multi_etend(end,end1, p+1, hi+1);
   //@ sorted_etend(end1, p+1, hi+1, p, get(end,p));
   //@ concat_array3(a,end,end0,set(end1,p,get(end,p)),lo,p,hi+1,get(end,p));
   //@ assert array_model(a,lo,hi+1,?res);
   //@ multiset_trans(end,start,res, lo, hi+1);
   /*/@ same_multi_ret(end, end1, p+1, hi+1);
   //@ concat_sorted2(end, end0, end1, lo, p, p+1, hi+1, get(end,p));
  	*/
  }
}
