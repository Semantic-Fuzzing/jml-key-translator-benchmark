// File: PositiveAccount.java
public class PositiveAccount {
    private int value;
    
    //@ requires x > 0;
    //@ ensures value == \old(value) + x;
        //@ requires x > 0;

    public void add(int x) {
        value += x;
    }
    
    //@ requires x > 0;
    //@ ensures \result == value;

    public int getValue() {
        return value;
    }
}