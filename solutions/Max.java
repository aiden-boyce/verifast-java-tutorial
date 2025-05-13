/**************************************************  
Part 1:    
    Define the Preconditions and Postconditions
    - Preconditions: 
        - requires ...
    - Postconditions: 
        - ensures ...
---------------------------------------------------
Part 2:
    Add Assertions
    - assert ...
**************************************************/

public class Max {
    public int max(int x, int y)
    //@ requires true;
    //@ ensures x <= result && y <= result;
    {
        int max;
        if(x <= y) 
            max = y;
        else 
            max = x;
        //@ assert x <= max && y <= max;
        return max;
    }

    public int max3(int x, int y, int z)
    //@ requires true;
    //@ ensures true;
    {
        int max = max(x, y);
        max = max(max, z);
        //@ assert x <= max && y <= max && z <= max;
        return max;
    }
}
