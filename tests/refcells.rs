extern crate core;
extern crate inert;

use core::cell::RefCell;
use inert::{Inert, NeutralizeMut, NeutralizeUnsafe};

#[test]
fn inert_new_mut() {
    let mut tree = tree();
    let inert = Inert::new_mut(&mut tree);

    assert_eq!(&**inert.name(), "premature optimisation");

    let wrath = &inert.children()[4];
    assert_eq!(&**wrath.name(), "wrath");

    let me = &wrath.children()[0];
    assert_eq!(&**me.name(), "nox");

    let best_language_ever = &inert.children()[0].children()[0];
    assert_eq!(&**best_language_ever.name(), "coq");
}

struct Node {
    name: String,
    children: Vec<RefCell<Node>>,
}

fn tree() -> RefCell<Node> {
    let mut root = Node::new("premature optimisation");

    let mut lust = Node::new("lust");
    lust.get_mut().append_child(Node::new("coq"));
    root.get_mut().append_child(lust);

    let mut gluttony = Node::new("gluttony");
    gluttony.get_mut().append_child(Node::new("chrome"));
    gluttony.get_mut().append_child(Node::new("slack"));
    gluttony.get_mut().append_child(Node::new("atom"));
    root.get_mut().append_child(gluttony);

    let mut greed = Node::new("greed");
    greed.get_mut().append_child(Node::new("airbnb"));
    greed.get_mut().append_child(Node::new("amazon"));
    greed.get_mut().append_child(Node::new("facebook"));
    greed.get_mut().append_child(Node::new("google"));
    greed.get_mut().append_child(Node::new("uber"));
    root.get_mut().append_child(greed);

    let mut sloth = Node::new("sloth");
    sloth.get_mut().append_child(Node::new("haskell"));
    root.get_mut().append_child(sloth);

    let mut wrath = Node::new("wrath");
    wrath.get_mut().append_child(Node::new("nox"));
    root.get_mut().append_child(wrath);

    let mut envy = Node::new("envy");
    envy.get_mut().append_child(Node::new("javascript"));
    root.get_mut().append_child(envy);

    let mut pride = Node::new("pride");
    pride.get_mut().append_child(Node::new("c"));
    pride.get_mut().append_child(Node::new("c++"));
    root.get_mut().append_child(pride);

    root
}

// FIXME(nox): Everything below that point should be generated through
// some sort of procedural macro.

unsafe impl NeutralizeUnsafe for Node {
    type Output = InertNode;

    unsafe fn neutralize_unsafe(&self) -> &Self::Output {
        &*(self as *const Self as *const Self::Output)
    }
}

struct InertNode {
    value: Node,
}
unsafe impl Sync for InertNode {}

unsafe impl NeutralizeMut for Node {}

impl InertNode {
    fn name(&self) -> &Inert<String> {
        // Compile check that tells us that `String` is `NeutralizeMut`.
        let _ = <Inert<String>>::new_mut;
        unsafe { Inert::new_unchecked(&self.value.name) }
    }

    fn children(&self) -> &Inert<Vec<RefCell<Node>>> {
        // Compile check that tells us that `Vec<RefCell<Node>>` is also
        // `NeutralizeMut`.
        let _ = <Inert<Vec<RefCell<Node>>>>::new_mut;
        unsafe { Inert::new_unchecked(&self.value.children) }
    }
}

impl Node {
    fn new(name: &str) -> RefCell<Self> {
        RefCell::new(Self { name: name.into(), children: vec![] })
    }

    fn append_child(&mut self, child: RefCell<Self>) {
        self.children.push(child);
    }
}