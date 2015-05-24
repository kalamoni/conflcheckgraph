public class Node {
	String name;
	int value;
	boolean noChild = false;
	boolean SingleParent = false;

	public Node() {
	}

	public Node(String name, int value) {
		this.name = name;
		this.value = value;
	}

	public static void main(String[] args) {

	}

	public String getName() {
		return this.name;
	}

	public void setName(String name) {
		this.name = name;
	}

	public int getValue() {
		return this.value;
	}

	public void setValue(int value) {
		this.value = value;
	}

	public boolean isNoChild() {
		return this.noChild;
	}

	public void setNoChild(boolean noChild) {
		this.noChild = noChild;
	}

	public boolean isSingleParent() {
		return this.SingleParent;
	}

	public void setSingleParent(boolean singleParent) {
		this.SingleParent = singleParent;
	}

	public String toString() {
		String name = "node label: " + this.getName() + " node value: "
				+ this.getValue() + " has children: " + this.isNoChild()
				+ " sinle parent: " + this.isSingleParent();
		return name;

	}
}
