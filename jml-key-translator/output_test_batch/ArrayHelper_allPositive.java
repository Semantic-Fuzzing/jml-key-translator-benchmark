public class ArrayHelper_allPositive {

    //@ requires arr != null;
    //@ ensures \result == (\forall int i; 0 <= i && i < arr.length; arr[i] > 0);
    public static boolean allPositive(int[] arr) {
        for (int num : arr) {
            if (num <= 0) return false;
        }
        return true;
    }
}