use super::lang::*;

enum Tree {
	Leaf(String),
	Branch(String, Vec<Box<Tree>>)
}

pub fn parse(input: String) -> Term<()> {
	use Tree:*;

	let mut tree = Leaf("nil");
	let mut focus = &mut tree;
	let lines = input.lines();

	for i in lines.len() {
		line = lines[i];

		match line {
			"ann" => {
				*focus = Branch("Ann", vec![Leaf("nil")]);
				if let Branch(_, ref mut branches) = *focus {
					focus = &mut branches[0];
				} else {
					panic!();
				}
			},
			"kind" => {
				*focus = Branch("Universe", vec![Leaf("nil")]);
				if let Branch(_, ref mut branches) = *focus {
					focus = &mut branches[0];
				} else {
					panic!();
				}
			},
			"var" => ,
			"rec" => ,
			"pi" => ,
			"fn" => ,
			"apply" => ,
			"sigma" => ,
			"pair" => ,
			"split" => ,
			"enum" => ,
			"lit" => ,
			"case" => ,
			"lazy" => ,
			"fold" => ,
			"unfold" =>
		}

		i += 1;
	}
}