public class OOPEXample {
    public static void main(String args[]) {
        A a = new B();
        // As get returns the class's n, and the get method is B's we get 2.
        // However a.n refers to A.n, which is 1. The field n is inherited from 
        // A, B adds another field called n.

        // Outputs: "a = new B(); a.get() -> 2, a.n -> 1"
        System.out.printf("A a = new B(); a.get() -> %d, a.n -> %d", a.get(), a.n);
    }
}

/**
 * A:
 * -> MLT: A.get (defined)
 * - int A.n     (defined)
 */
class A {
    public int n = 1;
    public int get() { return n; }
}

/**
 * A:
 * -> MLT: B.get (override)
 * - int A.n     (inherited)
 * - int B.n     (added)
 */
class B extends A {
    public int n = 2;
    public int get() { return n; }
}
