/**************************************************  
 * Remove "\" before "@"
 * Make sure there is no space between the comment 
 * tag and "@" symbol.
--------------------------------------------------- 
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

public class BankAccount {
    private int balance;

    public BankAccount()
    //\@ requires ...
    //\@ ensures ...
    {
        this.balance = 0;
    }

    public int getBalance()
    //\@ requires ...
    //\@ ensures ...
    {
        return this.balance;
    }

    public void deposit(int amount)
    //\@ requires ...
    //\@ ensures ...
    {
        this.balance += amount;
    }

    public void withdraw(int amount)
    //\@ requires ...
    //\@ ensures ...
    {
        this.balance -= amount;
    }

    public void transferTo(BankAccount other, int amount)
    //\@ requires ...
    //\@ ensures ...
    {
        this.withdraw(amount);
        other.deposit(amount);
    }
    
}
