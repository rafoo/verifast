//@ #include "vfarray.gh"

//@ #include "multiset.gh"

/*@
  
fixpoint array(int, int) array_swap(array(int, int) start, int i, int j) {
  return store(store(start, j, select(start, i)), i, select(start, j));
}
  

lemma void same_multiset_swap(array(int, int) start, int i, int j, int b, int e)
  requires b <= i &*& i < j &*& j < e;
  ensures same_multiset(start, array_swap(start, i, j), b, e);
{
   nat n = int_diff_always(b, e);
   int_diff_le(b, e, n);
   multiset<int> m = array_multiset(b, n, start);
   multiset<int> m2 = multiset_select_in(b, e, n, start, j);
   assert m == multiset_add(m2, select(start, j));
   same_multiset_store_in(b, e, n, start, m2, j, select(start, i));
   array(int, int) middle = store(start, j, select(start, i));
   assert array_multiset(b, n, middle) == multiset_add(m2, select(start, i));
   same_multiset_store_in(b, e, n, middle, m2, i, select(start, j));
   close same_multiset(start, array_swap(start, i, j), b, e);
}

lemma void swap_out(array(int, int) arr, int i, int j, int k)
  requires k != i &*& k != j;
  ensures select(array_swap(arr, i, j), k) == select(arr, k);
{ }

lemma void swap_in_i(array(int, int) arr, int i, int j)
  requires true;
  ensures select(array_swap(arr, i, j), i) == select(arr, j);
{ }

lemma void swap_in_j(array(int, int) arr, int i, int j)
  requires true;
  ensures select(array_swap(arr, i, j), j) == select(arr, i);
{ }

@*/

int select_c(int* arr, int key)
//@ requires array_model(arr, ?lo, ?hi, ?m) &*& lo <= key &*& key < hi;
//@ ensures array_model(arr, lo, hi, m) &*& select(m, key) == result;
{
      //@ array_model_select_unfold(arr,lo,hi,m,key);
      int res = *(arr+key);
      //@ array_model_select_fold(arr,lo,hi,m,key);
      return res;
}

void update(int* arr, int key, int val)
//@ requires array_model(arr, ?lo, ?hi, ?m) &*& lo <= key &*& key < hi;
//@ ensures array_model(arr, lo, hi, store(m, key, val));
{
      //@ array_model_select_unfold(arr,lo,hi,m,key);
      *(arr+key) = val;
      //@ array_model_store_fold(arr,lo,hi,m,key);
}


void swap (int* a, int i, int j)
//@ requires array_model(a, ?b, ?e, ?start) &*& b <= i &*& i < j &*& j < e;
//@ ensures array_model(a, b, e, array_swap(start, i, j));
{
  int aj = select_c(a, j);
  update(a, j, select_c(a, i));
  update(a, i, aj);
}

/*@ predicate minore(array(int,int) arr, int lo, int hi, int bound) =
	(lo>=hi) ? true :
	select(arr,hi-1) <= bound
	&*& minore(arr,lo,hi-1,bound);

    predicate majore(array(int,int) arr, int lo, int hi, int bound) = 
        (lo>=hi) ? true : 
	select(arr,lo) >= bound &*& majore(arr,lo+1,hi,bound);

    lemma void bound_empty_minore(array(int,int) arr, int lo, int hi, int bound)
      requires lo >= hi;
      ensures minore(arr,lo,hi,bound);
      {close minore(arr,lo,hi,bound);}
     
    lemma void bound_empty_majore(array(int,int) arr, int lo, int hi, int bound)
      requires lo >= hi;
      ensures majore(arr,lo,hi,bound);
      { close majore(arr,lo,hi,bound);}
      
    lemma void clear_minore(array(int, int) a, int lo, int hi, int bound)
    requires minore(a, lo, hi, bound);
    ensures true;
    {
      if (lo >= hi) { open minore(a, lo, hi, bound); } else {
      int i = hi;
      for (; i > lo; i--)
        invariant minore(a, lo, i, bound) &*& lo <= i &*& i <= hi;
        decreases i - lo;
        {
          open minore(a, lo, i, bound);
        }
        open minore(a, lo, lo, bound);
    }}

    lemma void clear_majore(array(int, int) a, int lo, int hi, int bound, nat n)
    requires majore(a, lo, hi, bound) &*& int_diff(lo, hi, n) == true;
    ensures true;
    {
      switch(n) {
        case zero: {
          open majore(a, lo, hi, bound);
        }
        case succ(p): {
          open majore(a, lo, hi, bound);
          clear_majore(a, lo+1, hi, bound, p);
        }
      }
    }

    lemma void minore_select(array(int, int) a, int lo, int hi, int bound, int i, nat l)
    requires minore(a, lo, hi, bound) &*& lo <= i &*& i < hi &*& int_diff(i, hi, l) == true;
    ensures minore(a, lo, hi, bound) &*& select(a, i) <= bound;
    {
       switch(l) {
         case zero: {
            open int_diff(i, hi, l);
            assert false;
         }
         case succ(p): {
            open minore(a, lo, hi, bound);
            if(i == hi-1) {
              close minore(a, lo, hi, bound);
            } else {
              int_diff_translate(i+1, hi, -1, p);
              minore_select(a, lo, hi-1, bound, i, p);
              close minore(a, lo, hi, bound);
            }
         }
       }

    }
/*
    lemma void minore_get(array(int, int) a, int lo, int hi, int bound, int i)
    requires minore(a, lo, hi, bound, _) &*& lo <= i &*& i < hi;
    ensures get(a, i) <= bound;
    {
      int j = hi-1;
      for (; j > i; j--)
        invariant i <= j &*& j <= hi &*& minore(a, lo, j+1, bound,_);
        decreases j - i;
        {
           open minore(a, lo, j+1, bound, _);
        } 
        open minore(a, lo, i+1, bound, _);
        clear_minore(a, lo, i, bound);
    }
*/
/*
   lemma void minore_left(array(int, int) a, int lo, int hi, int bound)
   requires get(a, lo) <= bound &*& minore(a, lo+1, hi, bound);
   ensures minore(a, lo, hi, bound);
   {
      int i = 
   
   
   }
*/

    lemma void minore_dup(array(int, int) a, int lo, int hi, int bound, nat length)
    requires minore(a, lo, hi, bound) &*& int_diff(lo, hi, length) == true;
    ensures minore(a, lo, hi, bound) &*& minore(a, lo, hi, bound);
    {
      switch(length) {
        case zero: {
           open minore(a, lo, hi, bound);
           close minore(a, lo, hi, bound);
           close minore(a, lo, hi, bound);
        }
        case succ(pred): {
           open minore(a, lo, hi, bound);
           int_diff_translate(lo+1, hi, -1, pred);
           minore_dup(a, lo, hi-1, bound, pred);
           close minore(a, lo, hi, bound);
           close minore(a, lo, hi, bound);        
        }
        }
    }

    lemma void minore_same_multiset(array(int,int) start, array(int, int) end, int lo, int hi, int bound, int i, nat length)
    requires same_multiset(start, end, lo, hi) &*& minore(start, lo, hi, bound) &*& int_diff(lo, i, length) == true &*& i <= hi;
    ensures same_multiset(start, end, lo, hi) &*& minore(start, lo, hi, bound) &*& minore(end, lo, i, bound);
    {
       switch(length) {
         case zero: {
           close minore(end, lo, i, bound);
         }
         case succ(pred): {
            int_diff_translate(lo+1, i, -1, pred);
            minore_same_multiset(start, end, lo, hi, bound, i-1, pred);
            same_multiset_sym(start, end, lo, hi);
            int j = same_multiset_assoc(end, start, lo, hi, i-1);
            same_multiset_sym(end, start, lo, hi);
            nat lj = int_diff_always(j, hi);
            minore_select(start, lo, hi, bound, j, lj);
            close minore(end, lo, i, bound);
         }
       
       }
    }

    lemma void one_more_bound_minore(array(int,int) arr, int lo, int hi, int bound)
    	requires minore(arr,lo,hi,bound) &*& select(arr,hi) < bound;
    	ensures minore(arr,lo,hi+1,bound);
    	{
    	   if (lo > hi) open minore(arr, lo, hi, bound);
    	   close minore(arr,lo,hi+1,bound);
    	}
    	
    lemma void one_more_bound_majore(array(int,int) arr, int lo, int hi, int bound)
    	requires majore(arr,lo,hi,bound) &*& select(arr,hi) >= bound;
    	ensures majore(arr,lo,hi+1,bound);
    	{ if (lo > hi) {
    	    open majore(arr,lo,hi,bound);
    	    close majore(arr,lo,hi+1,bound);
    	  } else if (lo == hi) {
    	    open majore(arr,lo,hi,bound);
    	    close majore(arr,lo+1,hi+1,bound);
    	    close majore(arr,lo,hi+1,bound);
    	  } else {
    	    open majore(arr,lo,hi,bound);
    	    one_more_bound_majore(arr,lo+1,hi,bound);
    	    close majore(arr,lo,hi+1,bound);
    	  }
        }
     
    lemma void one_more_bot_bound_majore(array(int,int) arr, int lo, int hi, int bound, int i, int j)
    	requires majore(arr,lo,hi,bound) &*& i == lo &*& j == hi &*& select(arr,j) <= bound;
    	ensures majore(array_swap(arr,i,j),lo+1,hi+1,bound);
    	{
    	
    	
   	   if(lo >= hi){
   	      open majore(arr,lo,hi,bound);
    	      close majore(array_swap(arr,i,j),lo+1,hi+1,bound);
    	   }else{
    	   /*
    	      int k = hi+1;
    	      open majore(arr,lo,hi,bound);
    	      close majore(array_swap(arr,i,j),k,hi+1,bound);
    	      for(;k > lo;k--)
    	        invariant k <= hi+1 &*& lo < k &*& majore(array_swap(arr,i,j),k,hi+1,bound) &*& majore(arr, lo+1, hi, bound);
    	        decreases (k-lo);
    	        {
    	          int g = lo+1;
    	          for(; g < k; g++)
	             invariant lo <= g &*& g <= k &*& majore(arr,g,hi,bound) &*& bound <= get(arr,g-1);
	             decreases ((hi+1)-g);
	             {
	             	if(g>= hi)
	             	  break;
	             	else {
	             	  open majore(arr,g,hi,bound);
	                }
	             }
	          close majore(arr,g,hi,bound);
	          assert (g == k-1);
	          assert get(arr,g-1) >= bound;
	          int h = g;
	          for(; h > lo; h--)
	             invariant h <= g &*& h >= lo &*& majore(arr,h,hi,bound);
	             decreases (h-(lo+1));
	             {
	                
	                  close majore(arr,h,hi,bound);
	                
	             }
	          assert (h==lo+1);
	          close majore(array_swap(arr,i,j),g,hi+1,bound);
    	   }*/ assume(false);
    	}
     }
         	
    lemma void minore_out_length(array(int,int) arr,int lo, int hi, int bound, int i, int j, nat length)
	requires minore(arr,lo,hi,bound) &*& hi <= i &*& hi <= j &*& int_diff(lo, hi, length) == true;
    	ensures minore(array_swap(arr,i,j),lo,hi,bound);
    	{
          switch (length) {
    	     case zero : {
    	       open minore(arr,lo,hi,bound);
    	       close minore(array_swap(arr,i,j),lo,hi,bound);
    	     }
    	     case succ(p) : {
    	       open minore(arr,lo,hi,bound);
    	       int_diff_translate(lo+1, hi, -1, p);
    	       minore_out_length(arr,lo,hi-1,bound,i,j,p);
    	       close minore(array_swap(arr,i,j),lo,hi,bound);
    	     }
    	   }
    	}

    lemma void minore_out(array(int,int) arr,int lo, int hi, int bound, int i, int j)
    	requires minore(arr,lo,hi,bound) &*& hi <= i &*& hi <= j;
    	ensures minore(array_swap(arr,i,j),lo,hi,bound);
    	{
    	  nat length = int_diff_always(lo, hi);
    	  minore_out_length(arr, lo, hi, bound, i, j, length);
    	}
    	
    lemma void majore_out(array(int,int) arr,int lo, int hi, int bound)
    	requires majore(arr,lo,hi,bound) &*& lo >= hi;
    	ensures majore(arr,lo+1,hi+1,bound);
    	{
    	open majore(arr,lo,hi,bound); 
    	close majore(arr,lo+1,hi+1,bound);}
   
    lemma void majore_top_less(array(int,int) arr,int lo, int hi, int bound, int j)
    	requires majore(arr,lo,hi,bound) &*& j <= hi;
    	ensures majore(arr,lo,j,bound);
    	{
    	  if (lo >= hi) {
    	     open majore(arr,lo,hi,bound);
    	     close majore(arr,lo,j,bound);
    	  } else if (lo >= j) {
    	     close majore(arr,lo,j,bound);
    	     nat n = int_diff_always(lo, hi);
    	     clear_majore(arr, lo, hi, bound, n);
    	  } else {
    	     open majore(arr,lo,hi,bound);
    	     majore_top_less(arr, lo+1, hi, bound, j);
    	     close majore(arr,lo,j,bound);
    	  }
    	}
    	
    lemma void majore_bot_less(array(int,int) arr,int lo, int hi, int bound)
    	requires majore(arr,lo,hi,bound);
    	ensures majore(arr,lo+1,hi,bound);
    	{ 
    	open majore(arr,lo,hi,bound);
    	if (hi <= lo){
    	  close majore(arr,lo+1,hi,bound);
    	}
    	}
    
    lemma void majore_top_more(array(int,int) arr,int lo,int hi,int bound)
    	requires majore(arr,lo,hi,bound) &*& select(arr,hi) >= bound;
    	ensures majore(arr,lo,hi+1,bound);
    	{
    	if(hi+1 <= lo){
    	  open majore(arr,lo,hi,bound);
    	  close majore(arr,lo,hi+1,bound);
    	} else if (hi == lo) {
    	  open majore(arr,lo,hi,bound);
    	  close majore(arr,lo+1,hi+1,bound);
    	  close majore(arr,lo,hi+1,bound);
    	} else {
          assert lo < hi;
    	  open majore(arr,lo,hi,bound);
    	  majore_top_more(arr,lo+1,hi,bound);
    	  close majore(arr,lo,hi+1,bound);
    	}
    }
    
    lemma void swap_majore(array(int,int) arr,int lo, int hi, int bound, int i, int j)
    	requires majore(arr,lo,hi,bound) &*& lo <= i &*& j < hi;
    	ensures majore(array_swap(arr,i,j),lo,hi,bound);
    	{
    	  if(hi <= lo){
    	     open majore(arr,lo,hi,bound);
    	     close majore(array_swap(arr,i,j),lo,hi,bound);
    	  }else{
    	     assume (false);
    	  }
    	}
@*/

int partition (int* a, int lo, int hi)
//@ requires array_model(a, lo, hi, ?start) &*& lo <= hi &*& *(a+hi) |-> ?p &*& p == select(start, hi);
/*@ ensures array_model(a, lo, hi+1, ?end) &*& same_multiset(start, end, lo, hi+1) &*&
      lo <= result &*& result <= hi &*&
      select(end, result) == p &*&
      minore(end, lo, result, select(end,result)) &*&
      majore(end, result+1, hi+1, select(end,result)); @*/
{
  int pivot = *(a+hi);
  int i = lo - 1;
  int j;
  //@ same_multiset_refl(start, lo, hi);
  //@ bound_empty_minore(start,lo,i+1,p);
  //@ bound_empty_majore(start,i+1,lo,p);
  for (j = lo; j < hi; j++) 
  /*@ invariant array_model(a,lo,hi,?arr) &*& lo <= j &*& j < hi+1 &*& i < j &*& lo -1 <= i &*& same_multiset(start, arr, lo, hi) &*& select(arr, hi) == p 
      &*& minore(arr,lo,i+1,p) &*& majore(arr,i+1,j,p); @*/
  { 
    int aj = select_c(a, j);
    if (aj < pivot) {
      i++;
      if (i < j) {
        swap(a, i, j);
        //@ same_multiset_swap(arr, i, j, lo, hi);
        //@ same_multiset_trans(start, arr, array_swap(arr, i, j), lo, hi);
        //@ swap_out(arr, i, j, hi);
        //@ swap_in_i(arr,i,j);
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
 //@ array_model_select_fold(a, lo, hi+1, arr, hi);
 //@ same_multiset_add_at_end(start, arr, lo, hi);
  if (i < hi) {
    swap(a, i, hi);
  //@ same_multiset_swap(arr, i, hi, lo, hi+1);
  //@ same_multiset_trans(start, arr, array_swap(arr, i, hi), lo, hi+1);
  //@ swap_in_i(arr, i, hi);
  //@ minore_out(arr, lo, i, p, i, hi);
  //@ swap_majore(arr, i, hi+1, p, i,hi);
  //@ majore_bot_less(array_swap(arr,i,hi), i, hi+1, p);
  }else{
  //@ majore_bot_less(arr, i, hi+1, p);
  }
  return i;
}

/*@ predicate sorted(array(int,int) arr,int b, int e) =
     (b >= e) ? true : 
     select(arr,b) <= select(arr,b+1) &*& sorted(arr,b+1,e);
    
    lemma void empty_sorted(array(int,int)arr,int b, int e)
    	requires b>=e;
    	ensures sorted(arr,b,e);
    	{ close sorted(arr,b,e);}
    	
/*    lemma void ensure_empty_array(int*a, int b,array(int,int) arr)
    	requires array_model(a,b,b,arr);
    	ensures true;
    	{open array_model(a,b,b,arr);} */
    	
    lemma void same_multi_etend(array(int,int) end, array(int,int) end1, int b, int e)
    	requires same_multiset(end,end1,b,e);
    	ensures same_multiset(end,store(end1,b-1, select(end,b-1)),b-1,e);
    	{assume(false);}
    	
    lemma void sorted_etend(array(int,int) end,int b, int e,int p,int v)
    	requires sorted(end,b,e) &*& p < b;
    	ensures sorted(store(end,p,v),b,e);
    	{assume(false);}
    	
    lemma void concat_array3(int*a, array(int,int) end, array(int,int) a0, array(int,int) a1, int b0, int e0, int e1, int bound)
    	requires array_model(a,b0,e0,a0) &*& array_model(a,e0,e1,a1) &*& same_multiset(end,a0,b0,e0) &*& same_multiset(end,a1,e0,e1) 
    		&*& sorted(a0,b0,e0) &*& sorted(a1,e0+1,e1) &*& minore(end,b0,e0,bound) &*& majore(end,e0+1,e1,bound) &*& bound == select(end,e0);
    	ensures array_model(a,b0,e1,?res) &*& same_multiset(res,end,b0,e1) &*& sorted(res,b0,e1);
    	{ assume(false);}
                     
     lemma void multiset_trans(array(int,int) arr, array(int,int) arr0, array(int,int) arr1, int b, int e)
     	requires same_multiset(arr0,arr,b,e) &*& same_multiset(arr1,arr,b,e);
     	ensures same_multiset(arr0,arr1,b,e);
     	{ same_multiset_sym(arr1, arr, b, e);
     	  same_multiset_trans(arr0, arr, arr1, b, e); }
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
   //@ array_model_select_unfold(a,lo,hi+1,start,hi);
   int p = partition(a, lo, hi);
   //@ assert array_model(a,lo,hi+1,?end);
   //@ array_model_select_unfold(a,lo,hi+1,end,p);
   quicksort(a, lo, p-1);
   //@ assert array_model(a,lo,p,?end0);
   quicksort(a, p+1, hi);
   //@ assert array_model(a,p+1,hi+1,?end1);
   //@ empty_array(a,p,end1);
   //@ array_model_store_fold(a,p,hi+1,end1,p);
   //@ open array_model(a, hi+1, hi+1, start);
   //@ same_multi_etend(end,end1, p+1, hi+1);
   //@ sorted_etend(end1, p+1, hi+1, p, select(end,p));
   //@ concat_array3(a,end,end0,store(end1,p, select(end,p)),lo,p,hi+1, select(end,p));
   //@ assert array_model(a,lo,hi+1,?res);
   //@ multiset_trans(end,start,res, lo, hi+1);
  }
}
