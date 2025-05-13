/**************************************************
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

    //@ predicate valid_counter(int c) = this.count |-> c;

    public Counter()
    //@ requires true;
    //@ ensures valid_counter(0);
    {
        this.count = 0;
        //@ close valid_counter(0);
    }

    public int getCount()
    //@ requires valid_counter(?c);
    //@ ensures valid_counter(c) &*& result == c;
    {
        return this.count;
    }

    public void increment()
    //@ requires valid_counter(?c);
    //@ ensures valid_counter(c + 1);
    {
        //@ open valid_counter(c);
        this.count += 1;
        //@ close valid_counter(_);
    }

    public void decrement()
    //@ requires valid_counter(?c);
    //@ ensures valid_counter(c - 1);
    {
        //@ open valid_counter(c);
        this.count -= 1;
        //@ close valid_counter(_);
    }

    public void increment_n_times(int n)
    //@ requires valid_counter(?c) &*& n >= 0;
    //@ ensures valid_counter(c + n);
    {
        int i = 0;
        while (i < n)
        //@ invariant i >= 0 && i <= n &*& valid_counter(c + i);
        {
            //@ open valid_counter(c + i);
            this.count += 1;
            //@ close valid_counter(c + i + 1);
            i++;
        }
    }
}
