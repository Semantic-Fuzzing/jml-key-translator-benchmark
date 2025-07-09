public class SafeDivider_factorial {

    //@ requires n >= 0;
    //@ ensures \result >= 0;
    public static int factorial(int n) {
        return (n == 0) ? 1 : n * factorial(n - 1);
    }
}