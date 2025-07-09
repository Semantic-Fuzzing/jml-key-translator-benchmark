import java.io.*;
import java.nio.file.*;
import java.util.*;
import com.spbu.jmltranslator.metrics.TokenCounter;

public class ComparisonMetrics {
    public static void main(String[] args) throws IOException {
        System.out.println("=== COMPARISON OF INPUT AND OUTPUT FILES ===\n");
        
        // Собираем метрики входных файлов
        Map<String, FileMetrics> inputMetrics = collectInputMetrics();
        
        // Собираем метрики выходных файлов
        Map<String, FileMetrics> outputMetrics = collectOutputMetrics();
        
        // Создаем сравнительную таблицу
        StringBuilder comparison = new StringBuilder();
        comparison.append(String.format("%-25s %-8s %-8s %-8s %-8s %-8s %-8s %-8s %-8s %-8s %-8s %-8s %-8s %-8s %-8s %-8s\n",
            "File", "InSizeKB", "OutSizeKB", "InTokens", "OutTokens", "InJMLAnn", "OutJMLAnn", 
            "InMethods", "OutMethods", "InFields", "OutFields", "InOld", "OutOld", "InQuant", "OutQuant", "InJMLTok", "OutJMLTok"));
        
        // Match input files with output files
        for (String inputFileName : inputMetrics.keySet()) {
            FileMetrics input = inputMetrics.get(inputFileName);
            
            // Find corresponding output files
            List<FileMetrics> matchingOutputs = findMatchingOutputs(inputFileName, outputMetrics);
            
            if (!matchingOutputs.isEmpty()) {
                // Sum metrics of all output files for this input
                FileMetrics totalOutput = sumOutputMetrics(matchingOutputs);
                
                comparison.append(String.format("%-25s %-8d %-8d %-8d %-8d %-8d %-8d %-8d %-8d %-8d %-8d %-8d %-8d %-8d %-8d %-8d\n",
                    inputFileName,
                    input.sizeKb, totalOutput.sizeKb,
                    input.tokens, totalOutput.tokens,
                    input.jmlAnn, totalOutput.jmlAnn,
                    input.methods, totalOutput.methods,
                    input.fields, totalOutput.fields,
                    input.old, totalOutput.old,
                    input.quant, totalOutput.quant,
                    input.jmlTok, totalOutput.jmlTok
                ));
            }
        }
        
        // Сохраняем результат
        Files.writeString(Path.of("../../reports/comparison_metrics.txt"), comparison.toString());
        System.out.println("Comparison metrics written to reports/comparison_metrics.txt\n");
        System.out.println(comparison);
        
        // Анализ изменений
        analyzeChanges(inputMetrics, outputMetrics);
    }
    
    private static List<FileMetrics> findMatchingOutputs(String inputFileName, Map<String, FileMetrics> outputMetrics) {
        List<FileMetrics> matches = new ArrayList<>();
        String baseName = inputFileName.replace(".java", "");
        
        for (String outputFileName : outputMetrics.keySet()) {
            if (outputFileName.startsWith(baseName + "_")) {
                matches.add(outputMetrics.get(outputFileName));
            }
        }
        
        return matches;
    }
    
    private static FileMetrics sumOutputMetrics(List<FileMetrics> metrics) {
        FileMetrics sum = new FileMetrics();
        for (FileMetrics metric : metrics) {
            sum.sizeKb += metric.sizeKb;
            sum.tokens += metric.tokens;
            sum.jmlAnn += metric.jmlAnn;
            sum.methods += metric.methods;
            sum.fields += metric.fields;
            sum.old += metric.old;
            sum.quant += metric.quant;
            sum.jmlTok += metric.jmlTok;
        }
        return sum;
    }
    
    private static Map<String, FileMetrics> collectInputMetrics() throws IOException {
        Map<String, FileMetrics> metrics = new HashMap<>();
        File dir = new File("../../examples/input");
        File[] files = dir.listFiles((d, name) -> name.endsWith(".java"));
        
        if (files != null) {
            for (File file : files) {
                String content = Files.readString(file.toPath());
                String fileName = file.getName();
                
                FileMetrics metric = new FileMetrics();
                metric.sizeKb = (int)Math.ceil(file.length() / 1024.0);
                metric.tokens = TokenCounter.countTotalTokens(content);
                metric.jmlAnn = TokenCounter.countJmlAnnotations(content);
                metric.methods = TokenCounter.countMethods(content);
                metric.fields = TokenCounter.countFields(content);
                metric.old = TokenCounter.countOldExpressions(content);
                metric.quant = TokenCounter.countQuantifiers(content);
                metric.jmlTok = TokenCounter.countJmlAnnotationTokens(content);
                
                metrics.put(fileName, metric);
            }
        }
        
        return metrics;
    }
    
    private static Map<String, FileMetrics> collectOutputMetrics() throws IOException {
        Map<String, FileMetrics> metrics = new HashMap<>();
        File dir = new File("../../examples/output");
        File[] files = dir.listFiles((d, name) -> name.endsWith(".java"));
        
        if (files != null) {
            for (File file : files) {
                String content = Files.readString(file.toPath());
                String fileName = file.getName();
                
                FileMetrics metric = new FileMetrics();
                metric.sizeKb = (int)Math.ceil(file.length() / 1024.0);
                metric.tokens = TokenCounter.countTotalTokens(content);
                metric.jmlAnn = TokenCounter.countJmlAnnotations(content);
                metric.methods = TokenCounter.countMethods(content);
                metric.fields = TokenCounter.countFields(content);
                metric.old = TokenCounter.countOldExpressions(content);
                metric.quant = TokenCounter.countQuantifiers(content);
                metric.jmlTok = TokenCounter.countJmlAnnotationTokens(content);
                
                metrics.put(fileName, metric);
            }
        }
        
        return metrics;
    }
    
    private static void analyzeChanges(Map<String, FileMetrics> input, Map<String, FileMetrics> output) {
        System.out.println("\n=== CHANGE ANALYSIS ===\n");
        
        int totalInputTokens = 0, totalOutputTokens = 0;
        int totalInputJMLTok = 0, totalOutputJMLTok = 0;
        int totalInputMethods = 0, totalOutputMethods = 0;
        
        for (String inputFileName : input.keySet()) {
            FileMetrics in = input.get(inputFileName);
            List<FileMetrics> matchingOutputs = findMatchingOutputs(inputFileName, output);
            
            if (!matchingOutputs.isEmpty()) {
                FileMetrics totalOut = sumOutputMetrics(matchingOutputs);
                
                totalInputTokens += in.tokens;
                totalOutputTokens += totalOut.tokens;
                totalInputJMLTok += in.jmlTok;
                totalOutputJMLTok += totalOut.jmlTok;
                totalInputMethods += in.methods;
                totalOutputMethods += totalOut.methods;
                
                double tokenRatio = in.tokens > 0 ? (double)totalOut.tokens / in.tokens : 0;
                double jmlRatio = in.jmlTok > 0 ? (double)totalOut.jmlTok / in.jmlTok : 0;
                
                System.out.printf("%s:\n", inputFileName);
                System.out.printf("  Tokens: %d → %d (ratio: %.2f)\n", in.tokens, totalOut.tokens, tokenRatio);
                System.out.printf("  JML tokens: %d → %d (ratio: %.2f)\n", in.jmlTok, totalOut.jmlTok, jmlRatio);
                System.out.printf("  Methods: %d → %d\n", in.methods, totalOut.methods);
                System.out.printf("  Output files: %d\n", matchingOutputs.size());
                System.out.println();
            }
        }
        
        System.out.printf("OVERALL STATISTICS:\n");
        System.out.printf("  Total tokens: %d → %d (ratio: %.2f)\n", 
            totalInputTokens, totalOutputTokens, (double)totalOutputTokens / totalInputTokens);
        System.out.printf("  JML tokens: %d → %d (ratio: %.2f)\n", 
            totalInputJMLTok, totalOutputJMLTok, (double)totalOutputJMLTok / totalInputJMLTok);
        System.out.printf("  Methods: %d → %d (ratio: %.2f)\n", 
            totalInputMethods, totalOutputMethods, (double)totalOutputMethods / totalInputMethods);
    }
    
    static class FileMetrics {
        int sizeKb, tokens, jmlAnn, methods, fields, old, quant, jmlTok;
    }
} 