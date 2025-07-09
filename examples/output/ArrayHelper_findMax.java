public class ArrayHelper_findMax {

    //@ requires arr != null && arr.length > 0;
    public static int findMax(int[] arr) {
        int max = arr[0];
        for (int num : arr) {
            if (num > max) max = num;
        }
        return max;
    }
}