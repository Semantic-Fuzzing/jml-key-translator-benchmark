import java.nio.file.*;
import com.spbu.jmltranslator.metrics.TokenCounter;

public class CountTest {
    public static void main(String[] args) throws Exception {
        System.out.println("=== TESTING COUNTS ===\n");
        
        // Test Account.java
        String accountContent = Files.readString(Path.of("../../examples/input/Account.java"));
        System.out.println("Account.java:");
        System.out.println("Fields: " + TokenCounter.countFields(accountContent));
        System.out.println("Old expressions: " + TokenCounter.countOldExpressions(accountContent));
        System.out.println("Quantifiers: " + TokenCounter.countQuantifiers(accountContent));
        System.out.println();
        
        // Test ArrayHelper.java
        String arrayHelperContent = Files.readString(Path.of("../../examples/input/ArrayHelper.java"));
        System.out.println("ArrayHelper.java:");
        System.out.println("Fields: " + TokenCounter.countFields(arrayHelperContent));
        System.out.println("Old expressions: " + TokenCounter.countOldExpressions(arrayHelperContent));
        System.out.println("Quantifiers: " + TokenCounter.countQuantifiers(arrayHelperContent));
        System.out.println();
        
        // Test MaxByElimination.java
        String maxByElimContent = Files.readString(Path.of("../../examples/input/MaxByElimination.java"));
        System.out.println("MaxByElimination.java:");
        System.out.println("Fields: " + TokenCounter.countFields(maxByElimContent));
        System.out.println("Old expressions: " + TokenCounter.countOldExpressions(maxByElimContent));
        System.out.println("Quantifiers: " + TokenCounter.countQuantifiers(maxByElimContent));
    }
} 