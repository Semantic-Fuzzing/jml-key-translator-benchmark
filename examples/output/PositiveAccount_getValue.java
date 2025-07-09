public class PositiveAccount_getValue {
    private int value;

    //@ ensures \result == value;
    public int getValue() {
        return value;
    }
}