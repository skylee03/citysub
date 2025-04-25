/* Basic Types and Operations */

name = "Alice";
"Hello " + name + "!";

cond = true;
if cond then "Yes" else "No";

();
() as Top;

/* Function Types */

greet = fn name : String.
  "Hello " + name + "!";
greet name;

/* Record Types */

Animal = {
  name : String,
  eat : Unit -> String
};

Cat = {
  name : String,
  eat : Unit -> String,
  meow : Unit -> String
};

catty = {
  name = "Catty",
  eat = fn _ : Unit. "Catty is eating!",
  meow = fn _ : Unit. "Catty is meowing!"
} as Cat;

Dog = {
  name : String,
  eat : Unit -> String,
  woof : Unit -> String
};

doggy = {
  name = "Doggy",
  eat = fn _ : Unit. "Doggy is eating!",
  woof = fn _ : Unit. "Doggy is woofing!"
} as Dog;

/* Variant Types and Pattern Matching */

Pet = <
  cat : Cat,
  dog : Dog
>;

makeSound = fn pet : Pet.
  case pet of
    <cat = someCat> => someCat.meow
  | <dog = someDog> => someDog.woof;

makeSound <cat = catty> as Pet ();
makeSound <dog = doggy> as Pet ();

/* Universal Types */

id = fn T <: Top. fn x : T.
  x;
id [String];
id [String] "Hello";