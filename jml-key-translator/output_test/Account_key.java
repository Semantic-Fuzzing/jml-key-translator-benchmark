public class Account_deposit {
    private int balance;

    //@ ghost int __old_balance_0 = (int)balance;
    //@ requires amount > 0;
    //@ ensures balance == ((int)__old_balance_0) + amount;
    public int deposit(int amount) {
        balance += amount;
        return balance;
    }
}
