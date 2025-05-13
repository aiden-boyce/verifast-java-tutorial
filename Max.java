/**************************************************  
 * Remove "\" before "@"
 * Make sure there is no space between the comment 
 * tag and "@" symbol.
--------------------------------------------------- 
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
    //\@ requires ...
    //\@ ensures ...
    {
        int max;
        if(x <= y) 
            max = 0;
        else 
            max = x;
        //\@ assert ...
        return max;
    }

    public int max3(int x, int y, int z)
    //\@ requires ...
    //\@ ensures ...
    {
        int max = max(x, y);
        max = max(max, z);
        //\@ assert ...
        return max;
    }
}
