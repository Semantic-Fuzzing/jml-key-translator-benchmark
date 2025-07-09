import java.nio.file.*;
import com.spbu.jmltranslator.metrics.TokenCounter;

public class TokenDebug {
    public static void main(String[] args) throws Exception {
        System.out.println("=== DEBUG TOKEN COUNTING ===\n");
        
        // Test ArrayHelper.java
        String arrayHelperContent = Files.readString(Path.of("../../examples/input/ArrayHelper.java"));
        System.out.println("ArrayHelper.java content:");
        System.out.println(arrayHelperContent);
        System.out.println("---");
        System.out.println("Total tokens: " + TokenCounter.countTotalTokens(arrayHelperContent));
        System.out.println("JML annotation tokens: " + TokenCounter.countJmlAnnotationTokens(arrayHelperContent));
        System.out.println("JML annotations count: " + TokenCounter.countJmlAnnotations(arrayHelperContent));
        System.out.println();
        
        // Test Max.java
        String maxContent = Files.readString(Path.of("../../examples/input/Max.java"));
        System.out.println("Max.java content:");
        System.out.println(maxContent);
        System.out.println("---");
        System.out.println("Total tokens: " + TokenCounter.countTotalTokens(maxContent));
        System.out.println("JML annotation tokens: " + TokenCounter.countJmlAnnotationTokens(maxContent));
        System.out.println("JML annotations count: " + TokenCounter.countJmlAnnotations(maxContent));
    }
} 