enum StackOp<StackAlphabet> {
    Pop,
    Push(StackAlphabet),
}

#[repr(transparent)]
#[derive(Clone, Debug)]
struct PDAStack<StackAlphabet: Clone> {
    vec: Vec<StackAlphabet>,
}

impl <StackAlphabet: Clone> Default for PDAStack<StackAlphabet> {
    fn default() -> PDAStack<StackAlphabet>{
	PDAStack { vec: vec![] }
    }
}

impl <StackAlphabet: Clone> PDAStack<StackAlphabet> {
    pub fn apply(&mut self, s: Option<StackOp<StackAlphabet>>) {
	match s {
	    None => {},
	    Some(StackOp::Pop) => { self.vec.pop(); },
	    Some(StackOp::Push(x)) => { self.vec.push(x) }
	};
    }
    pub fn peek(&self) -> Option<StackAlphabet> {
	self.vec.last().map(|x| x.clone())
    }
}



struct Dest<State, StackAlphabet>(Option<State>, Option<StackOp<StackAlphabet>>);
struct Source<State, StackAlphabet, InputAlphabet>(State, Option<StackAlphabet>, InputAlphabet);

trait PDA {
    type State: Default + Clone;
    type InputAlphabet: Clone;
    type StackAlphabet: Clone;
    fn advance(source: Source<Self::State, Self::StackAlphabet, Self::InputAlphabet>) -> Dest<Self::State, Self::StackAlphabet>;

    fn run<T: IntoIterator<Item=V>, V: Into<Self::InputAlphabet>>(input: T) -> PDARunner<Self> where Self: Sized {
	PDARunner::<Self>::run(input)
    }
}

#[derive(Debug)]
struct PDARunner<T: PDA> {
    state: T::State,
    stack: PDAStack<T::StackAlphabet>,
}

impl <T: PDA> Default for PDARunner<T> {
    fn default() -> PDARunner<T> {
	PDARunner {
	    state: Default::default(),
	    stack: Default::default(),
	}
    }
}

impl <T:PDA> PDARunner<T> {
    fn update_state(&mut self, state: Option<T::State>) {
	if let Some(state) = state {
	    self.state = state
	}
    }
    fn advance(&mut self, inp: T::InputAlphabet) {
	let source = Source::<T::State, T::StackAlphabet, T::InputAlphabet>(self.state.clone(), self.stack.peek(), inp);
	let Dest(state, stack) = T::advance(source);
	self.update_state(state);
	self.stack.apply(stack);
    }
    pub fn run<X: IntoIterator<Item=V>, V: Into<T::InputAlphabet>>(input: X) -> Self {
	let mut s: Self = Default::default();
	for i in input.into_iter() {
	    s.advance(i.into())
	}
	s
    }
}

mod balanced_parens {
    use super::{Source, Dest, PDA, StackOp};

    #[derive(Debug, Clone)]
    pub enum Stack {
	Parens
    }
    #[derive(Clone, Debug)]
    pub enum State {
	Ok,
	Error,
    }
    impl Default for State {
	fn default() -> State {
	    State::Ok
	}
    }
    #[derive(Clone, Debug)]
    pub enum Input {
	Other,
	LeftParens,
	RightParens
    }
    impl From<char> for Input {
	fn from(c: char) -> Input {
	    match c {
		'(' => Self::LeftParens,
		')' => Self::RightParens,
		_ => Self::Other,
	    }
	}
    }
    #[derive(Debug)]
    pub struct BalancedParensPDA;
    impl PDA for BalancedParensPDA {
	type State = State;
	type InputAlphabet = Input;
	type StackAlphabet = Stack;
	fn advance(src: Source<Self::State, Self::StackAlphabet, Self::InputAlphabet>) -> Dest<Self::State, Self::StackAlphabet> {
	    match src {
		Source(State::Error, _, _) => Dest(None, None),
		Source(_, _, Input::Other) => Dest(None, None),
		Source(State::Ok, _, Input::LeftParens) => Dest(None, Some(StackOp::Push(Stack::Parens))),
		Source(State::Ok, Some(Stack::Parens), Input::RightParens) => Dest(None, Some(StackOp::Pop)),
		Source(State::Ok, _, Input::RightParens) => Dest(Some(State::Error), None),
	    }
	}
    }

}

use balanced_parens::BalancedParensPDA;

fn balanced(data: &str) -> bool {
    data.chars().map(|x| match x {
	'(' => 1,
	')' => -1,
	_ => 0
    }).fold(0, |acc, x| {
	if acc < 0 {
	    acc
	} else {
	    acc + x
	}
    }) == 0
}


fn main() {
    let pdar = BalancedParensPDA::run("()".chars());
    println!("{:?}", pdar);
}
