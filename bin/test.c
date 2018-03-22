#include <stdlib.h>

struct account {
  int balance;
  int limit;
};

/*@
predicate account_pred(struct account *myAccount, int theLimit, int theBalance) =
  myAccount->limit |-> theLimit &*& myAccount->balance |-> theBalance
  &*& malloc_block_account(myAccount);
@*/

struct account *create_account(int b)
//@ requires true;
//@ ensures account_pred(result,b,0);
{
  struct account *myAccount = malloc(sizeof(struct account));
  if(myAccount == 0) { abort(); }
  myAccount->balance=0;
  myAccount->limit=b;
  return myAccount;
  //@close account_pred(myAccount,b,0);
}

void account_dispose(struct account *myAccount)
//@ requires account_pred(myAccount,_,_);
//@ ensures emp;
{
//@ open account_pred(myAccount,_,_);
  free(myAccount);
}

int account_withdraw(struct account *myAccount,int less)
//@ requires account_pred(myAccount, ?limit, ?balance);
//@ ensures (balance-less < limit ? (result == balance-limit &*& account_pred(myAccount,limit,limit)) : (result == less &*& account_pred(myAccount,limit,balance-less)));
{
 int b = account_get_balance(myAccount);
 //@ open account_pred(myAccount,limit,balance);
 if(b-less < myAccount->limit){
   myAccount->balance=myAccount->limit;
   return b - myAccount->limit;
   //@ close account_pred(myAccount,limit,limit);
 }else{
   myAccount->balance = b-less;
   return less;
   //@ close account_pred(myAccount,limit,b-less);
 }
}

int account_get_balance(struct account *myAccount)
//@ requires account_pred(myAccount, ?limit, ?balance);
//@ ensures account_pred(myAccount, limit, balance) &*& result == balance;
{
//@ open account_pred(myAccount,limit,balance);
  return myAccount->balance;
  //@ close account_pred(myAccount,limit,balance);
}

void account_deposit(struct account *myAccount,int amount)
//@ requires account_pred(myAccount, ?limit, ?balance) &*& 0 <= amount;
//@ ensures account_pred(myAccount, limit, balance + amount);
{
  //@ open account_pred(myAccount, limit, balance);
  myAccount->balance += amount;
  //@ close account_pred(myAccount, limit, balance + amount);
}

int main(void)
//@ requires true;
//@ ensures true;
{
  struct account *myAccount = create_account(-100);
  account_deposit(myAccount,200);
  int w1 = account_withdraw(myAccount,50);
  assert(w1==50);
  int b1 = account_get_balance(myAccount);
  assert(b1==150);
  int w2 = account_withdraw(myAccount,300);
  assert(w2 == 250);
  int b2 = account_get_balance(myAccount);
  assert(b2 == -100);
  account_dispose(myAccount);
  return 0;
}	