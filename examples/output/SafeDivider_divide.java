public class SafeDivider_divide {

    //@ requires y != 0;
    //@ ensures \result == x / y;
    public static int divide(int x, int y) {
        return x / y;
    }
}