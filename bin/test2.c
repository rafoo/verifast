#include <stdlib.h>

struct node {
	struct node *next;
	int value;
};

struct stack {
	struct node *head;
};


/*@
inductive ints = ints_nil | ints_cons(int, ints);

predicate nodes(struct node *node, ints num) =
	node == 0 ?
	num == ints_nil :
	num == ints_cons(?number,?num2) &*& node -> next |-> ?next &*& node->value |-> number
	&*& malloc_block_node(node) &*& nodes(next,num2);
	
predicate stack(struct stack *stack, ints num) =
	stack->head |-> ?head &*& malloc_block_stack(stack) &*& nodes(head,num);

predicate nodesOld(struct node *node, int count) =
	node==0 ? 
	count == 0 : 
	count > 0 &*& node->next |-> ?next &*& node->value |-> ?value
	&*& malloc_block_node(node) &*& nodesOld(next,count-1);

predicate stackOld(struct stack *stack, int count) =
	stack->head |-> ?head &*& malloc_block_stack(stack) &*& count >= 0 &*& nodesOld(head,count);
	

@*/

bool stack_is_empty(struct stack *stack)
//@ requires stackOld(stack, ?count);
//@ ensures stackOld(stack,count) &*& result == (count == 0);
{
	//@open stackOld(stack,count);
	struct node *h = stack->head;
	//@open nodesOld(h,count);
	bool result = stack->head == 0;
	//@close nodesOld(h,count);
	//@close stackOld(stack,count);
	return result;
}

struct stack* create_stack()
//@ requires true;
//@ ensures stackOld(result,0);
{
	struct stack *s=malloc(sizeof(struct stack));
	if(s==0){abort();}
	s->head=0;
	return s;
	//@ close nodesOld(0,0);
	//@ close stackOld(s,0);
}

struct stack* create_stackInd()
//@ requires true;
//@ ensures stack(result,ints_nil);
{
	struct stack *s=malloc(sizeof(struct stack));
	if(s==0){abort();}
	s->head=0;
	return s;
	//@ close nodes(0,ints_nil);
	//@ close stack(s,ints_nil);
}

void stack_push(struct stack *s,int add)
//@ requires stackOld(s,?count);
//@ ensures stackOld(s,count+1);
{
	//@open stackOld(s,count);
	struct node *res = malloc(sizeof(struct node));
	if(res==0){abort();}
	res->value=add;
	res->next=s->head;
	s->head=res;
	//@ close nodesOld(res,count+1);
	//@ close stackOld(s,count+1);
}

void stack_pushInd(struct stack *s,int add)
//@ requires stack(s,?count);
//@ ensures stack(s,ints_cons(add,count));
{
	//@open stack(s,count);
	struct node *res = malloc(sizeof(struct node));
	if(res==0){abort();}
	res->value=add;
	res->next=s->head;
	s->head=res;
	//@ close nodes(res,ints_cons(add,count));
	//@ close stack(s,ints_cons(add,count));
}

int stack_pop(struct stack *s)
//@ requires stackOld(s,?count) &*& count > 0;
//@ ensures stackOld(s,count-1);
{
	//@open stackOld(s,count);
	struct node *h =s->head;
	//@ open nodesOld(h,count);
	int res = h->value;
	s->head=h->next;
	free(h);
	return res;
	//@close stackOld(s,count-1);
}
/*@
 fixpoint int ints_head(ints values) {
  switch (values) {
    case ints_nil: return 0;
    case ints_cons(value,values0): return value;
  }
}

fixpoint ints ints_tail(ints values){
  switch (values) {
    case ints_nil: return ints_nil;
    case ints_cons(value,values0): return values0;
  }
}
@*/
int stack_popInd(struct stack *s)
//@ requires stack(s,?count) &*& count != ints_nil;
//@ ensures stack(s,ints_tail(count)) &*& result == ints_head(count);
{
	//@open stack(s,count);
	struct node *h =s->head;
	//@ open nodes(h,count);
	int result = h->value;
	s->head=h->next;
	free(h);
	//@close stack(s,ints_tail(count));
	return result;
}

void stack_popn(struct stack *s, int i)
//@ requires stackOld(s,?count) &*& count >= i &*& i > 0;
//@ ensures stackOld(s,count - i);
{
  int j = 0;
  while(j != i )
  //@ invariant stackOld(s,count-j) &*& i>=j;
  {
    stack_pop(s);
    j++;
  }
}

void stack_disposeInd(struct stack *stack)
//@ requires stack(stack, ints_nil);
//@ ensures true;
{
  //@ open stack(stack, ints_nil);
  //@ open nodes(_,_);
  free(stack);
}

void stack_dispose(struct stack *s)
//@requires stackOld(s,?count) &*& count >= 0;
//@ensures emp;
{
	if(stack_is_empty(s)){
		//@open stackOld(s,0);
		//@open nodesOld(_,_);
		free(s);
	}else{
		stack_pop(s);
		stack_dispose(s);
	}
}

void stack_dispose2(struct stack *s)
//@ requires stackOld(s,_);
//@ ensures true;
{
 //@ open stackOld(s,_);
 struct node *n = s -> head;
 while (n != 0)
  //@ invariant nodesOld(n,_);
 {
  //@ open nodesOld(n,_);
  struct node *next = n->next;
  free(n);
  n = next;
 }
 //@ open nodesOld(0,_);
 free(s);
}

int stack_get_sum(struct stack *s)
//@ requires stackOld(s,?count) &*& count >= 0;
//@ ensures stackOld(s,count);
{
	int i = 0;
	if(!stack_is_empty(s)){
		i = stack_pop(s);
		int j = stack_get_sum(s);
		stack_push(s,i);
		i += j;
	}
	return i;
}

/*@
  fixpoint int ints_sum(ints values){
    switch (values){
      case ints_nil: return 0;
      case ints_cons(value,values0): return value + ints_sum(values0);
    }
  }      
@*/

int nodes_get_num(struct node *n)
//@ requires nodes(n,?count);
//@ ensures nodes(n,count) &*& result == ints_sum(count);
{

     //@ open nodes(n,count);
   int i=0;
   if(n!=0){
     i = n->value;
     int j = nodes_get_num(n->next);
     i += j;
   }
   
     //@ close nodes(n,count);
   return i;
}
int stack_get_sumInd(struct stack *s)
//@ requires stack(s,?count);
//@ ensures stack(s,count) &*& result == ints_sum(count);
{
  //@ open stack(s,count);
  int res = nodes_get_num(s->head);
  return res;
  //@ close stack(s,count);
}

int main()
//@ requires true;
//@ ensures true;
{
	struct stack *s = create_stackInd();
	stack_pushInd(s,10);
	stack_pushInd(s,20);
	int result1 = stack_popInd(s);
	assert(result1 == 20);
	int result2 = stack_popInd(s);
	assert(result2 == 10);
	stack_disposeInd(s);
	return 0;
}