fn my_function() {
    // a owns the string object
    let a = String::from("This is my string");

    // c owns the string object
    let c = String::from("Keep me!");

    { // start of a new scope
        // a transfers ownership to b
        let b = a;
        
        // a is no longer valid - it owns no data, we cannot use it anymore

        // b's scope ends here, so the string is now dropped
    }
    
    // end of the function scope, c is dropped
}

fn show(a: String) {
    // a now owns the string

    // a gives a reference of the string to println to allow it to print
    println!("The string is: {}", a)

    // a goes out of scope, and the string is dropped
}

fn print_my_string() {
    let my_string = String::from("This is my string");

    show(my_string);
    
    // we cannot use a anymore - the value it owned has been given to show

}

fn bar(a: &i32) -> &str {
    match a {
        0 => "none",
        1 => "single",
        2 => "double",
        _ => "more"
    }
}

fn zig(n: &mut i32) {
    *n += 1
    // n goes out of scope, but nothing is dropped
}

fn foo() {
    let mut a = 3; // we borrow mutably later so must be mut
    {
        let b = &a;        // b borrows a reference to a
        let c = bar(b);    // c takes b (a reference) and 
        // b goes out of scope, c goes out of scope and the string is dropped
    }

    zig(&mut a); // a is incremented
    // a goes out of scope
}

fn bing() { // Scope a starts here
    let mut num_1: Option<&i32> = None;

    { // Scope b starts here
        let num_2 = 7;
        num_1 = Some(&num_2);

        // num_2 is dropped here
    }
    // num_1 no longer valid - it contains a reference to num_2 but outlives num_2
}

#[derive(Debug)]
struct PersonID<'a> {
    name: &'a str,
    id_ref: &'a str,
    age: u8
}

fn zapp<'a>() {
    let mut bob : PersonID<'a> = PersonID {name: "bob", id_ref: "120dd", age: 99};

    {
        let new_name = String::from("jimmy");
        // bob.name = &new_name;
        bob.age = 8;
    }
}

fn jib(s: String) -> i32 {
    42
}

fn zing() {
    let mut nums = vec![1,2,3,4];

    // add is mutable - each call changes nums, it captures a mutable reference to nums
    let mut add = |n| nums.push(n);

    for x in 0..=10 {
        add(x)
    }
    
    // we can now use a mutable reference to nums, add is not used after / can be considered dropped
    nums.push(3);
}

fn zang() {
    let mut nums = vec![1,2,3,4];

    // add is mutable - each call changes nums, it captures a mutable reference to nums
    let mut add = move |n| nums.push(n);
    // we cannot use nums from here onwards - it has been moved into add
    
    for x in 0..=10 {
        add(x)
    }
}

fn captures() {
    let a = String::from("hello world");
    
    let c = || jib(a);

    // println!("Hello {}", a);
}

fn main() {}