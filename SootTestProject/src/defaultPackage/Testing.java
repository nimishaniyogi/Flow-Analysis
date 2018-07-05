
public class Testing {
	
	int[] heapArray;
    /** size of array **/
    private int maxSize; 
    /** number of nodes in array **/
    private int heapSize; 
	static int chk;
    /** Constructor **/
    public Testing() 
    {
        maxSize = 10;
        heapSize = 0;
        heapArray = new int[maxSize]; 
    }
    
    public boolean isEmpty() 
    {
        return heapSize == 0;
    }
    /** Function to insert element **/
    
    public int insert(int ele) 
    {
        if (heapSize + 1 == maxSize)
            return 0;
        heapArray[++heapSize] = ele;
        int pos = heapSize;
        while (pos != 1 && ele > heapArray[pos/2])
        {
            heapArray[pos] = heapArray[pos/2];
            pos /=2;
        }
        heapArray[pos] = ele;    
        return ele;
    }
    
    public void displayHeap()
    {
        /* Array format */
        System.out.print("\nHeap array: ");    
        for(int i = 1; i <= heapSize; i++)
            System.out.print(heapArray[i] +" ");
        System.out.println("\n");
    }
    
    public static void main(String[] args) {
    	Testing t = new Testing();
    	int total = 0;
		for (int i = 0; i < 10; i++){
			chk = t.insert(10);
			total = total + t.heapArray[i];
			t.displayHeap();
			System.out.println("Total : "+total);
		}
//		HeapTest.someStaticField = "Some Text";

	}
}
