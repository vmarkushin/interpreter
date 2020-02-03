use crate::Token;
use std::fmt;

pub enum Node<T> {
    Branch {
        value: T,
        left: Option<Box<Node<T>>>,
        right: Option<Box<Node<T>>>,
    },
    Leaf {
        value: T,
    }
}
/*
impl<T> Node<T> {
    pub fn branch(value: T, left) -> Box<Self> {
        Box::new(
            Node::Branch {
                value, left, right })
    }
}
*/
struct Tree<T> {
    pub root: Node<T>
}

impl<T: fmt::Debug> fmt::Debug for Tree<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("!")
    }
}

type TokenTree = Tree<Token>;

#[test]
fn debug_output_test() {
    let tree = Tree {
        root: Node::Branch {
            value: 0,
            left: Some(Box::new(
                Node::Leaf {
                    value: 1,
                })),
            right: Some(Box::new(
                Node::Leaf {
                    value: 2,
                })),

        }
    };
    println!("{:?}", tree);
    panic!();
    
}
