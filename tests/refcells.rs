use std::cell::RefCell;
use inert::{Inert, NeutralizeMut};

#[test]
fn inert_new_mut() {
    let mut tree = tree();
    let inert = Inert::new_mut(&mut tree);

    assert_eq!(inert.name().0, "premature optimisation");

    let wrath = &inert.children()[4];
    assert_eq!(wrath.name().0, "wrath");

    let me = &wrath.children()[0];
    assert_eq!(me.name().0, "nox");

    let best_language_ever = &inert.children()[0].children()[0];
    assert_eq!(best_language_ever.name().0, "coq");
}

#[inert::neutralize(as unsafe InertNode)]
struct Node {
    #[inert::field]
    name: Name,
    #[inert::field]
    children: Vec<RefCell<Node>>,
}

#[inert::neutralize(as Self)]
struct Name(String);

impl Node {
    fn new(name: &str) -> RefCell<Self> {
        RefCell::new(Self { name: Name(name.into()), children: vec![] })
    }

    fn append_child(&mut self, child: RefCell<Self>) {
        self.children.push(child);
    }
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

// FIXME(nox): We should be able to derive that impl, so that the getter
// can type check that their return type does indeed implement `NeutralizeMut`
// themselves.
unsafe impl NeutralizeMut for Node {}
