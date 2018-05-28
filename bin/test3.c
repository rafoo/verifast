//@#include "vfarray.gh"
//@#include "multiset.gh"

int main(void)
//@ requires true;
//@ ensures true;
{
	int a[10];

	
	//@ array_model_init(a, 10);
	//@ assert array_model(a, 0, 10, ?t);
	//@ array_model_select_unfold(a, 0, 10, t, 2);

	a[2] = 1;
	//@ array_model_store_fold(a, 0, 10, t, 2);
	//@ assert array_model(a, 0, 10, ?t2);
	//@ assert select(t2, 2) == 1;
	//@ array_model_delete(a, 10);
	return 0;
}
