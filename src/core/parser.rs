use super::language::*;

enum Tree {
	Usage(Usage),
	Branch(Vec<Box<Tree>>)
}

pub fn parse(input: String) -> Term<()> {
	use Tree:*;

	let mut tree = Branch(Vec::new());
	let mut focus = &mut tree.0;
	let lines = input.lines();

	for i in lines.len() {
		line = lines[i];

		match line {
			"ann" => focus = ,
			"kind" => ,
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