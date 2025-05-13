/**************************************************
 * Remove "\" before "@"
 * Make sure there is no space between the comment 
 * tag and "@" symbol.
--------------------------------------------------- 
Part 1:    
    Define a Field Ownership Predicate
    - predicate v(x) = this.f |-> x
    Modify the Value in the Predicate
    - open v(x)
    - close v(x)
---------------------------------------------------
Part 2:
    Define a Loop Invariant in increment_n_times(n)
**************************************************/

public class Counter {
    private int count;

    //\@ predicate ...

    public Counter()
    //\@ requires ...
    //\@ ensures ...
    {
        this.count = 0;
    }

    public int getCount()
    //\@ requires ...
    //\@ ensures ...
    {
        return this.count;
    }

    public void increment()
    //\@ requires ...
    //\@ ensures ...
    {
        this.count += 1;
    }

    public void decrement()
    //\@ requires ...
    //\@ ensures ...
    {
        this.count -= 1;
    }

    public void increment_n_times(int n)
    //\@ requires ...
    //\@ ensures ...
    {
        int i = 0;
        while (i < n)
        //\@ invariant ...
        {
            this.count += 1;
            i++;
        }
    }
}
