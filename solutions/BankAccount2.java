/**************************************************  
Part 1:
    Define the Preconditions and Postconditions
    with Field Ownership
    - this.f |-> x
---------------------------------------------------
Part 2:
    Define a Field Ownership Predicate
    - predicate v(x) = this.f |-> x
    Modify the Value in the Predicate
    - open v(x)
    - close v(x)
**************************************************/

public class BankAccount2 {
    private int balance;

    //@ predicate valid_act(int b) = this.balance |-> b;

    public BankAccount2()
    //@ requires true;
    //@ ensures valid_act(0);
    {
        this.balance = 0;
        //@ close valid_act(0);
    }

    public int getBalance()
    //@ requires valid_act(?b);
    //@ ensures valid_act(b) &*& result == b;
    {
        return this.balance;
    }

    public void deposit(int amount)
    //@ requires valid_act(?b);
    //@ ensures valid_act(b + amount);
    {
        //@ open valid_act(b);
        this.balance += amount;
        //@ close valid_act(_);
    }

    public void withdraw(int amount)
    //@ requires valid_act(?b);
    //@ ensures valid_act(b - amount);
    {
        //@ open valid_act(b);
        this.balance -= amount;
        //@ close valid_act(_);
    }

    public void transferTo(BankAccount2 other, int amount)
    /*@ requires this.valid_act(?tB) &*&
        other != null &*&
        other.valid_act(?oB); @*/
    /*@ ensures this.valid_act(tB - amount) &*&
        other.valid_act(oB + amount); @*/
    {
        this.withdraw(amount);
        other.deposit(amount);
    }
    
}
