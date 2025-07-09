public class Account {
    private int balance;
    
    //@ requires amount > 0;
    //@ ensures balance == \old(balance) + amount;

    public int deposit(int amount) {
        balance += amount;
        return balance;
    }
}