import java.io.*;
import java.nio.file.*;
import java.util.*;
import com.spbu.jmltranslator.metrics.TokenCounter;

public class InputTestMetrics {
    public static void main(String[] args) throws IOException {
        File dir = new File("../../examples/input");
        File[] files = dir.listFiles((d, name) -> name.endsWith(".java"));
        if (files == null) {
            System.out.println("No test files found.");
            return;
        }
        StringBuilder table = new StringBuilder();
        table.append(String.format("%-25s %-8s %-8s %-8s %-8s %-8s %-8s %-8s %-8s\n",
            "File", "SizeKB", "Tokens", "JMLAnn", "Methods", "Fields", "Old", "Quant", "JMLTok"));
        for (File file : files) {
            String content = Files.readString(file.toPath());
            int sizeKb = (int)Math.ceil(file.length() / 1024.0);
            int tokens = TokenCounter.countTotalTokens(content);
            int jmlAnn = TokenCounter.countJmlAnnotations(content);
            int methods = TokenCounter.countMethods(content);
            int fields = TokenCounter.countFields(content);
            int old = TokenCounter.countOldExpressions(content);
            int quant = TokenCounter.countQuantifiers(content);
            int jmlTok = TokenCounter.countJmlAnnotationTokens(content);
            table.append(String.format("%-25s %-8d %-8d %-8d %-8d %-8d %-8d %-8d %-8d\n",
                file.getName(), sizeKb, tokens, jmlAnn, methods, fields, old, quant, jmlTok));
        }
        Files.writeString(Path.of("../../reports/input_test_metrics.txt"), table.toString());
        System.out.println("Input test metrics written to reports/input_test_metrics.txt\n");
        System.out.println(table);
    }
} 