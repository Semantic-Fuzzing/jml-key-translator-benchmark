public class memory_test {
    public static void main(String[] args) {
        Runtime runtime = Runtime.getRuntime();
        
        System.out.println("=== JVM MEMORY TEST ===");
        System.out.println("Max memory: " + runtime.maxMemory() / (1024 * 1024) + " MB");
        System.out.println("Total memory: " + runtime.totalMemory() / (1024 * 1024) + " MB");
        System.out.println("Free memory: " + runtime.freeMemory() / (1024 * 1024) + " MB");
        System.out.println("Used memory: " + (runtime.totalMemory() - runtime.freeMemory()) / (1024 * 1024) + " MB");
        
        // Create objects
        System.out.println("\nCreating objects...");
        String[] strings = new String[1000];
        for (int i = 0; i < 1000; i++) {
            strings[i] = "Test string " + i + " with some content to use memory";
        }
        
        System.out.println("After creating objects:");
        System.out.println("Used memory: " + (runtime.totalMemory() - runtime.freeMemory()) / (1024 * 1024) + " MB");
        
        // Force GC
        System.out.println("\nCalling GC...");
        System.gc();
        
        System.out.println("After GC:");
        System.out.println("Used memory: " + (runtime.totalMemory() - runtime.freeMemory()) / (1024 * 1024) + " MB");
    }
} 