// verifast_options{disable_overflow_check prover:z3v4.5 target:Win64}


package com.company;

class Node {
    static final boolean RED = true;
    static final boolean BLACK = false;

    int data;
    Node parent;
    Node left;
    Node right;
    boolean color;

    Node(int data) 
    //@ requires true;
    //@ ensures this.data |-> data &*& this.left |-> null &*& this.right |-> null &*& this.color |-> true &*& this.parent |-> null;
    {
        this.data = data;
        this.parent = null;
        this.left = null;
        this.right = null;
        this.color = RED;
    }

    public String toString() {
        
        String color = this.color ? "RED" : "BLACK";
        return "Node{" +
                "data=" + data +
                ", color=" + color +
                ", left=" + left +
                ", right=" + right +
                "}";
    }
}

/*@

predicate valid_rb_tree(Node n, rbtree t) = 
    switch (t) {
        case nilNode : return n == null;
        case node(val, color, left, right): return 
            n.data |-> ?v &*& 
            n.color |-> ?c &*& 
            n.left |-> ?l &*& 
            n.right |-> ?r &*&
            n.parent |-> ?p &*&
            valid_rb_tree(l, left) &*& 
            valid_rb_tree(r, right) &*& 
            n != null &*& 
            v == val &*&
            noConsecutiveReds(left, color) == true &*&
            noConsecutiveReds(right, color) == true;
    } &*& sorted(t) == true &*& correctBlackHeight(t);


predicate correctBlackHeight(rbtree t) =
    switch(t) {
        case nilNode: return true;
        case node(val, color, left, right): return (blackHeight(left) == blackHeight(right) && blackHeight(left) > 0 && blackHeight(right) > 0);
    };

inductive rbtree =
| nilNode
| node(int, boolean, rbtree, rbtree);

fixpoint int blackHeight(rbtree t) {
    switch(t) {
        case nilNode: return 1;
        case node(val, color, left, right): return (blackHeight(left) == blackHeight(right) &&
                                                    blackHeight(left) > 0 && blackHeight(right) > 0)
        ? 
        (blackHeight(left) + (color ? 0 : 1))
        :
        0;
    }
}

fixpoint boolean noConsecutiveReds(rbtree t, boolean parentColor) {
    switch(t) {
        case nilNode: return true;
        case node(val, color, left, right): return (parentColor == true && color == true) ? false : noConsecutiveReds(left, color) && noConsecutiveReds(right, color);
    }
}

fixpoint int max(rbtree t) {
    switch(t) {
        case nilNode: return 0;
        case node(val, color, left, right): return (right == nilNode ? val : max(right));
    }
}

fixpoint int min(rbtree t) {
    switch(t) {
        case nilNode: return 0;
        case node(val, color, left, right): return (left == nilNode ? val : min(left));
    }
}

fixpoint boolean sorted(rbtree t) {
    switch(t) {
        case nilNode: return true;
        case node(val, color, left, right): return (left == nilNode ? true : max(left) < val) && (right == nilNode ? true : val < min(right)) && sorted(left) && sorted(right);
    }
}

fixpoint boolean rb_tree_contains(rbtree t, int value) {
    switch(t) {
        case nilNode: return false;
        case node(val, color, left, right): return (val == value) ? true : (rb_tree_contains(left, val) || rb_tree_contains(right, val));
    }
}

fixpoint int size(rbtree t) {
    switch(t) {
        case nilNode: return 0;
        case node(val, color, left, right): return 1 + size(left) + size(right);
    }
}

// should do the same as the fixinsert method
fixpoint rbtree fixInsert(rbtree t) {
    return t;
}

// should encapsulate the logic for deleting, replacing the deleted node and then fixing the rb tree if its invalid
fixpoint rbtree handleDelete(rbtree t) {
    return t;
}

fixpoint rbtree rb_tree_add(rbtree t, int inserted) {
    switch(t) {
        case nilNode: return node(inserted, true, nilNode, nilNode);
        case node(val, color, left, right): return val < inserted ?
            fixInsert(node(val, color, rb_tree_add(left, inserted), right)) : 
            val == inserted ?
                node(val, color, left, right) :
                fixInsert(node(val, color, left, rb_tree_add(right, inserted)));
    }
}

fixpoint rbtree rb_tree_delete(rbtree t, int deleted) {
    switch(t) {
        case nilNode: return nilNode;
        case node(val, color, left, right): return deleted == val ?
            handleDelete(t) :
            deleted < val ?
                node(val, color, rb_tree_delete(left, deleted), right) :
                node(val, color, left, rb_tree_delete(right, deleted));
    }
}

@*/

public class RedBlackTree {
    
    private Node root;

    public RedBlackTree() 
    //@ requires true;
    //@ ensures this.root |-> ?r;
    {
        this.root = null;
    }

    public Node getRoot()
    //@ requires this.root |-> ?r &*& valid_rb_tree(r, ?t);
    //@ ensures valid_rb_tree(r, t);
    {
        return root;
    }

    public void insert(int key)
    // requires this.root |-> ?r &*& valid_rb_tree(r, ?t);
    // ensures valid_rb_tree(r, rb_tree_add(t, key));
    {
        Node insert = new Node(key);
        Node parent = null;
        Node current = this.root;

        while (current != null) 
        //@ invariant valid_rb_tree(current, ?c);
        {
            //@ open valid_rb_tree(current, c);
            if (key == current.data) {
                //@ close valid_rb_tree(r, rb_tree_add(t, key));
                return;
            }
            
            parent = current;
            // Traversing down to the right spot
            if (key < current.data) {
                current = current.left;
            } else {
                current = current.right;
            }
        }

        insert.parent = parent;
        // No parent means no nodes
        if (parent == null) {
            root = insert;
        } else if (insert.data < parent.data) {
            parent.left = insert;
        } else {
            parent.right = insert;
        }
    
        // size of tree is 1 bigger than before
        // tree should be sorted at this point
        // also contains the key

        if (parent == null) {
            insert.color = Node.BLACK;
            //@ close valid_rb_tree(r, rb_tree_add(t, key));
            return;
        }

        if (insert.parent.parent == null) {
            //@ close valid_rb_tree(r, rb_tree_add(t, key));
            return;
        }
        fixInsert(insert);
        //@ close valid_rb_tree(r, rb_tree_add(t, key));
    }

    private void fixInsert(Node node) 
    // requires true;
    // ensures valid_rb_tree(node, ?t);
    {
        Node uncle;
        while (node.parent.color == Node.RED) {
            if (node.parent == node.parent.parent.right) {
                uncle = node.parent.parent.left;
                if (uncle.color == Node.RED) {
                    uncle.color = Node.BLACK;
                    node.parent.color = Node.BLACK;
                    node.parent.parent.color = Node.RED;
                    node = node.parent.parent;
                } else {
                    if (node == node.parent.left) {
                        node = node.parent;
                        rightRotate(node);
                    }
                    node.parent.color = Node.BLACK;
                    node.parent.parent.color = Node.RED;
                    leftRotate(node.parent.parent);
                }
            } else {
                uncle = node.parent.parent.right;

                if (uncle.color == Node.RED) {
                    uncle.color = Node.BLACK;
                    node.parent.color = Node.BLACK;
                    node.parent.parent.color = Node.RED;
                    node = node.parent.parent;
                } else {
                    if (node == node.parent.right) {
                        node = node.parent;
                        leftRotate(node);
                    }
                    node.parent.color = Node.BLACK;
                    node.parent.parent.color = Node.RED;
                    rightRotate(node.parent.parent);
                }
            }
            if (node == root) {
                break;
            }
        }
        root.color = Node.BLACK;
    }

    
    private void rightRotate(Node node)
    {
        Node left = node.left;
        node.left = left.right;
        if (left.right != null) {
            left.right.parent = node;
        }
        left.parent = node.parent;
        transplant(node, left);
        node.parent = left;
    }

    private void leftRotate(Node node)
    {
        Node right = node.right;
        node.right = right.left;
        if (right.left != null) {
            right.left.parent = node;
        }
        right.parent = node.parent;
        transplant(node, right);
        node.parent = right;
    }


    public void preOrder() 
    {
        System.out.println("Preorder traversal:");
        preOrderHelper(this.root);
        System.out.println("");
    }

    private void preOrderHelper(Node node) {
        if (node != null) {
            System.out.print(node.data + " ");
            preOrderHelper(node.left);
            preOrderHelper(node.right);
        }
    }

    public void postOrder() {
        System.out.println("Postorder traversal:");
        postOrderHelper(this.root);
        System.out.println("");

    }

    private void postOrderHelper(Node node) {
        if (node != null) {
            postOrderHelper(node.left);
            postOrderHelper(node.right);
            System.out.print(node.data + " ");
        }
    }

    public void inOrder() {
        System.out.println("Inorder traversal:");
        inOrderHelper(this.root);
        System.out.println("");
    }

    private void inOrderHelper(Node node) {
        if (node != null) {
            inOrderHelper(node.left);
            System.out.print(node.data + " ");
            inOrderHelper(node.right);
        }
    }

    public boolean delete(int key) 
    // requires this.root |-> ?r &*& valid_rb_tree(r, t);
    // ensures valid_rb_tree(r, rb_tree_delete(t, key));
    {
        Node node = search(key);
        if (node != null) {
            deleteNode(node);
            return true;
        } else {
            return false;
        }
    }

    private void deleteNode(Node node) 
    // requires valid_rb_tree(n, ?t);
    // ensures valid_rb_tree(n, rb_tree_delete(t, node.data));
    {
        Node prev = node;
        Node x;
        boolean prevOriginalColor = prev.color;

        if (node.left == null) {
            x = node.right;
            transplant(node, node.right);
        } else if (node.right == null) {
            x = node.left;
            transplant(node, node.left);
        } else {
            prev = minimum(node.right);
            prevOriginalColor = prev.color;
            x = prev.right;
            if (prev.parent == node) {
                x.parent = prev;
            } else {
                transplant(prev, prev.right);
                prev.right = node.right;
                prev.right.parent = prev;
            }
            transplant(node, prev);
            prev.left = node.left;
            prev.left.parent = prev;
            prev.color = node.color;
        }

        if (prevOriginalColor == Node.BLACK) {
            deleteFixup(x);
        }
    }

    private void deleteFixup(Node prev) 
    // requires true;
    // ensures valid_rb_tree(prev, ?t);
    {
        while (prev != root && prev.color == Node.BLACK) {
            if (prev == prev.parent.left) {
                Node sib = prev.parent.right;

                if (sib.color == Node.RED) {
                    sib.color = Node.BLACK;
                    prev.parent.color = Node.RED;
                    leftRotate(prev.parent);
                    sib = prev.parent.right;
                }

                if (sib.left.color == Node.BLACK && sib.right.color == Node.BLACK) {
                    sib.color = Node.RED;
                    prev = prev.parent;
                } else {
                    if (sib.right.color == Node.BLACK) {
                        sib.left.color = Node.BLACK;
                        sib.color = Node.RED;
                        rightRotate(sib);
                        sib = prev.parent.right;
                    }

                    sib.color = prev.parent.color;
                    prev.parent.color = Node.BLACK;
                    sib.right.color = Node.BLACK;
                    leftRotate(prev.parent);
                    prev = root;
                }
            } else {
                Node sib = prev.parent.left;

                if (sib.color == Node.RED) {
                    sib.color = Node.BLACK;
                    prev.parent.color = Node.RED;
                    rightRotate(prev.parent);
                    sib = prev.parent.left;
                }

                if (sib.right.color == Node.BLACK && sib.left.color == Node.BLACK) {
                    sib.color = Node.RED;
                    prev = prev.parent;
                } else {
                    if (sib.left.color == Node.BLACK) {
                        sib.right.color = Node.BLACK;
                        sib.color = Node.RED;
                        leftRotate(sib);
                        sib = prev.parent.left;
                    }

                    sib.color = prev.parent.color;
                    prev.parent.color = Node.BLACK;
                    sib.left.color = Node.BLACK;
                    rightRotate(prev.parent);
                    prev = root;
                }
            }
        }

        prev.color = Node.BLACK;
    }

    private void transplant(Node original, Node newNode) {
        if (original.parent == null) {
            root = newNode;
        } else if (original == original.parent.left) {
            original.parent.left = newNode;
        } else {
            original.parent.right = newNode;
        }
        if (newNode != null) {
            newNode.parent = original;
        }
    }

    private Node minimum(Node node) {
        while (node.left != null) {
            node = node.left;
        }
        return node;
    }

    // cannot use result -> data == key but dont know why
    public Node search(int key) 
    // requires this.root |-> ?r &*& valid_rb_tree(r, ?t);
    // ensures valid_rb_tree(r, t) &*& result == null ? true : result -> data == key;
    {
        Node result = search(key, root);
        return result;
    }

    private Node search(int key, Node node) 
    // requires valid_rb_tree(node, ?t);
    // ensures valid_rb_tree(node, t) &*& result == null ? true : result -> data == key;
    {
        //@ open valid_rb_tree(node, t);
        if (node == null) {
            //@ close valid_rb_tree(node, t);
            return null;
        }
        
        if (node.data == key) {
            Node result = node;
            //@ close valid_rb_tree(result, t);

            return result;
        } else {
            Node result;
            if (key < node.data) {
                //@ open valid_rb_tree(node.left, ?l);
                //@ close valid_rb_tree(node.left, l);
                result = search(key, node.left);
            } else {
                //@ open valid_rb_tree(node.right, ?r);
                //@ close valid_rb_tree(node.right, r);
                result = search(key, node.right);
            }
            //@ close valid_rb_tree(node, t);
            return result;
        }
    }


    
    public boolean verifyRedBlackProperties() 
    // requires valid_rb_tree(node, ?t);
    // ensures valid_rb_tree(node, ?t) &*& result == true;
    {
        boolean valid = checkBlackHeight(root) > 0;
        if (valid) {
            valid = checkNoConsecutiveRed(root, Node.BLACK);
        }
        return valid;
    }

    private int checkBlackHeight(Node node)
    // requires valid_rb_tree(node, ?t);
    // ensures valid_rb_tree(node, t) &*& result > 0;
    {
        //@ open valid_rb_tree(node, t);
        if (node == null) {
            return 1;
            //@ close valid_rb_tree(node, t);
        }
        Node left = node.left;
        Node right = node.right;
        //@ open valid_rb_tree(left, ?l);
        //@ close valid_rb_tree(left, l);
        int leftBlackHeight = checkBlackHeight(left);

        //@ open valid_rb_tree(right, ?r);
        //@ close valid_rb_tree(right, r);
        int rightBlackHeight = checkBlackHeight(right);

        // Check if the black height of the left and right subtrees is the same,
        if (leftBlackHeight == rightBlackHeight && leftBlackHeight > 0 && rightBlackHeight > 0) {
            int result = leftBlackHeight + (node.color ? 0 : 1);
            
            return result;
            //@ close valid_rb_tree(node, t);
        } else {
            // assert false doesnt work here
            //@ assert false;
            // violation, will propagate
            return 0;
        }
    }

    private boolean checkNoConsecutiveRed(Node node, boolean parentColor)
    // requires valid_rb_tree(node, ?t);
    // ensures valid_rb_tree(node, t) &*& result == true;
    {
        //@ open valid_rb_tree(node, t);
        if (node == null) {
            //@ close valid_rb_tree(node, t);
            return true;
        }
        // two red nodes
        if (node.color == Node.RED && parentColor == Node.RED) {
            // ?? again assert false doesnt work
            //@ assert false;
            return false;
        }

        Node left = node.left;
        Node right = node.right;

        //@ open valid_rb_tree(left, ?l);
        //@ close valid_rb_tree(left, l);
        boolean leftB = checkNoConsecutiveRed(left, node.color);
        //@ open valid_rb_tree(right, ?r);
        //@ close valid_rb_tree(right, r);
        boolean rightB = checkNoConsecutiveRed(right, node.color); 
        //@ close valid_rb_tree(node, t);
        return leftB && rightB;
    }
}
