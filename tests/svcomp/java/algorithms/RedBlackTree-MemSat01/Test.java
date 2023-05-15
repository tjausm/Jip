import rbtree.RedBlackTree;
import rbtree.RedBlackTreeNode;

public class Test {
	
	public static void main(String[] args) {

		try {
			RedBlackTree tree = new RedBlackTree();

			for (int i = 0; i < 10; i++) {
				int data = 2*i;
				tree.treeInsert(new RedBlackTreeNode(data));
				System.out.println("inserting") ;
			}
			System.out.println("done") ;
			int data = 7 ;
			RedBlackTreeNode node = tree.treeSearch(tree.root(), data);
			System.out.println("done searching") ;
		} catch (Exception e) {
			throw new Error();
		}
	}

}
