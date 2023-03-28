use std::{fmt, io, fs, collections::HashMap};
use logos::Logos;
use num_bigint::BigInt;

static HELP_TEXT: &str = r#"
Useful tool for register machines in the Imperial College Computing Course (year 2).

Can run register machines by parsing from files (very fast due to logos).

Register machine syntax is:
INC Rb Lc    :->: La : Rb+ -> Lc
DEC Rb Lc Ld :->: La : Rb- -> Lc, Ld
HALT         :->: La : HALT

Options for this helper are:
help    - help menu (will display this text 😊)
load    - add new register machine from file, provide name
rm      - remove register machine
eval    - evaluate from initial configuration (L, R, R, R) etc
"#;

/// Tokenising register machine input
#[derive(Logos, Debug, PartialEq)]
enum RegTok {
  #[token("DEC")]
  Dec,

  #[token("INC")]
  Inc,

  #[token("HALT")]
  Halt,

  #[regex("R[0-9]+", |lex| lex.slice()[1..].parse())]
  Reg(u64),

  #[regex("L[0-9]+", |lex| lex.slice()[1..].parse())]
  Label(u64),

  #[regex(r"[ \r\t\n\f]", logos::skip)]
  WhiteSpace,

  #[error]
  Error,
}

enum RegOp {
  Inc(u64, u64),
  Dec(u64, u64, u64),
  Halt,
}

impl fmt::Debug for RegOp {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
      match self {
        RegOp::Inc(r, l2) => write!(f, "R{}+ -> L{}", r, l2),
        RegOp::Dec(r, l2, l3) => write!(f, "R{}- -> L{}, L{}", r, l2, l3),
        RegOp::Halt => write!(f, "HALT"),
    }
  }
}

type RegProgram = Vec<RegOp>;

/// Takes user input, to determine which mode, files etc.
fn main() {
  println!("{}",HELP_TEXT);

  let mut user_input = String::new();
  let mut reg_machines : HashMap<String, RegProgram> = HashMap::new();

  loop {
    println!("Select Option:");
    io::stdin().read_line(&mut user_input).expect("Invalid Input");
    match user_input.trim() {
      "help" => println!("{}",HELP_TEXT),
      "load" => {
        println!("Name of register machine: ");
        let mut name = String::new();
        io::stdin().read_line(&mut name).expect("Invalid Input");

        println!("File to load: ");
        user_input.clear();
        io::stdin().read_line(&mut user_input).expect("Invalid Input");
        if let Ok(content ) = fs::read_to_string(user_input.trim()) {
          if let Some(prog) = load_regmachine(content) {
            reg_machines.insert(name, prog);
          }
        } else {
          println!("Could not read from the file.");
        }
      }
      "rm" => {
        println!("Enter the name of the Register Machine to remove:");
        user_input.clear();
        io::stdin().read_line(&mut user_input).expect("Invalid Input");
        
        match reg_machines.remove(&user_input) {
            Some(_) => println!("Removed {}", user_input.trim()),
            None => println!("{} was not loaded", user_input.trim()),
        }
      }
      "lst" => {
        println!("printing register machines:");
        for (k, _) in &reg_machines {
          println!("{}", k);
        }
      }
      "eval" => {
        println!("Enter the name of the Register Machine run:");
        user_input.clear();
        io::stdin().read_line(&mut user_input).expect("Invalid Input");

        match reg_machines.get(&user_input) {
          Some(prog) => evaluate_regmachine(prog),
          None => println!("No register machine called {} is loaded.", user_input.trim()),
        }
      }
        // "enc<<"
        // "dec<<"
        // "enc<"
        // "dec<"
        // "decrm"
        // "encrm"
        // "enclstrm"
        // "encinstr"
      "quit" => break,
      _ => println!("what??!")
    }
    user_input.clear();
  }
}

/// Load a register machine from a string.
fn load_regmachine(raw_text : String) -> Option<RegProgram> {
  let mut program : RegProgram = vec![];
  let mut lex = RegTok::lexer(raw_text.as_str());

  println!("\nInstructions:");
  loop {
    match lex.next() {
      Some(RegTok::Inc) => {
        // label Inc Reg Label
        if let Some(RegTok::Reg(r)) = lex.next() {
          if let Some(RegTok::Label(l2)) = lex.next() {
            program.push(RegOp::Inc(r,l2));
            continue;
          }
        }
        print!("error at {}", lex.slice());
        break None;
      },
      Some (RegTok::Dec) => {
        // label Dec Reg Label Label
        if let Some(RegTok::Reg(r)) = lex.next() {
          if let Some(RegTok::Label(l2)) = lex.next() {
            if let Some(RegTok::Label(l3)) = lex.next() {
              program.push(RegOp::Dec(r, l2, l3));
              continue;
            }
          }
        }
        print!("error at {}", lex.slice());
        break None;
      },
      Some (RegTok::Halt) => {
        program.push(RegOp::Halt);
        continue;
      },
      Some(RegTok::WhiteSpace) => continue,
      None => {
        for p in &program {
          println!("{:?}", p);
        }
        break Some(program)},
      _ => {
        println!("error at {}", lex.slice());
        break None;
      },
    }
  }
}

/// evaluate a register machine.
fn evaluate_regmachine(prog : &RegProgram) {
  println!("Please enter the initial label");
  let mut user_input = String::new();
  io::stdin().read_line(&mut user_input).expect("Invalid Input");
  let mut cur_instr : u64;

  if let Ok(a) = user_input.trim().parse() {
    cur_instr = a;
  } else {
    println!("Invalid label");
    return;
  }

  let mut registers : Vec<u64> = Vec::new();

  println!("Setup register values (type non-number to finish adding):");
  loop {
    println!("Register {}:", registers.len());
    user_input.clear();
    io::stdin().read_line(&mut user_input).expect("Invalid Input");
    match user_input.trim().parse::<u64>() {
        Ok(a) => registers.push(a),
        Err(_) => break,
    }
  }
  
  println!("Starting Program");


  loop {

    if cur_instr as usize >= prog.len() {
      println!("Erroneous halt, no instruction at label {}", cur_instr);
    }

    print!("L:{} ", cur_instr);
    for (r,v) in registers.iter().enumerate() {
      print!("| R{}: {}", r, v);
    }
    
    println!(" -> run {:?}", prog[cur_instr as usize]);
    match prog[cur_instr as usize] {
      RegOp::Inc(r, l) => {
        if r as usize > registers.len() {
          println!("Malformed program, cannot execute");
          return;
        }
        registers[r as usize] += 1;
        cur_instr = l;
      },
      RegOp::Dec(r, l1, l2) => {
        if r as usize > registers.len() {
          println!("Malformed program, cannot execute");
          return;
        }
        
        if registers[r as usize] > 0 {
          registers[r as usize] -= 1;
          cur_instr = l1;
        } else {
          cur_instr = l2;
        }
      },
      RegOp::Halt => {
        println!("{:?} - Program complete", RegOp::Halt);
        return;
      },
    }
  }
}