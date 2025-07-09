public class PositiveAccount_add {
    private int value;

    //@ ghost int __old_value_0 = (int)value;
    //@ requires x > 0;
    //@ ensures value == ((int)__old_value_0) + x;
    public void add(int x) {
        value += x;
    }
}