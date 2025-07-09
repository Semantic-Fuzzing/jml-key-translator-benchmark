// File: SafeDivider.java
public class SafeDivider {
    
    //@ requires y != 0;
    //@ ensures \result == x / y;

    public static int divide(int x, int y) {
        return x / y;
    }
    
    //@ requires n >= 0;
    //@ ensures \result >= 0;

    public static int factorial(int n) {
        return (n == 0) ? 1 : n * factorial(n - 1);
    }
}