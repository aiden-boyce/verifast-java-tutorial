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

public class BankAccount1 {
    private int balance;

    public BankAccount1()
    //@ requires true;
    //@ ensures this.balance |-> 0;
    {
        this.balance = 0;
    }

    public int getBalance()
    //@ requires this.balance |-> ?b;
    //@ ensures this.balance |-> b &*& result == b;
    {
        return this.balance;
    }

    public void deposit(int amount)
    //@ requires this.balance |-> ?b;
    //@ ensures this.balance |-> b + amount;
    {
        this.balance += amount;
    }

    public void withdraw(int amount)
    //@ requires this.balance |-> ?b;
    //@ ensures this.balance |-> b - amount;
    {
        this.balance -= amount;
    }

    public void transferTo(BankAccount1 other, int amount)
    /*@ requires this.balance |-> ?tB &*&
        other != null &*&
        other.balance |-> ?oB; @*/
    /*@ ensures this.balance |-> tB - amount &*&
        other.balance |-> oB + amount; @*/
    {
        this.withdraw(amount);
        other.deposit(amount);
    }
    
}
