// File: ArrayHelper.java
public class ArrayHelper {
    //@ requires arr != null;
    //@ ensures \result == (\forall int i; 0 <= i && i < arr.length; arr[i] > 0);
    public static boolean allPositive(int[] arr) {
        for (int num : arr) {
            if (num <= 0) return false;
        }
        return true;
    }
    
    //@ requires arr != null && arr.length > 0;
    //@ ensures \result == (\max int i; 0 <= i && i < arr.length; arr[i]);
    public static int findMax(int[] arr) {
        int max = arr[0];
        for (int num : arr) {
            if (num > max) max = num;
        }
        return max;
    }
}