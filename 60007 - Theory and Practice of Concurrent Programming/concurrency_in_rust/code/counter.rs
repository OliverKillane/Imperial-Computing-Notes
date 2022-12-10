use std::{thread, sync::{Arc, Mutex}};

fn main() {
    let counter = Arc::new(Mutex::new(0));

    (1..10)
        .map(|_| counter.clone())
        .map(|i: Arc<Mutex<i32>>| thread::spawn(move || *i.lock().unwrap() += 1))
        .map(|t| t.join().unwrap()).for_each(drop);
    
    println!("Final value: {}", *counter.lock().unwrap())
}
