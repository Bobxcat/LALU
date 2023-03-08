use std::{
    fs::{read_to_string, File},
    io::{Read, Write},
};

use lalu_asm::{instruction_set::InstructionSet, interpret::Runtime};

fn main() -> std::io::Result<()> {
    const BIN_FILE: &str = "out.lalu";

    let in_file = {
        let mut args = std::env::args();
        args.next();
        match args.next() {
            Some(path) => path,
            None => "in.txt".into(),
        }
    };

    println!("Reading assembly from file: {in_file}");

    let raw = read_to_string(in_file)?;
    let ins = InstructionSet::from_string(raw);
    // println!("=====Instructions=====\n{ins:#?}");

    println!("Writing binary to file: {BIN_FILE}");
    File::create(BIN_FILE)
        .unwrap()
        .write_all(&ins.to_bytes())
        .unwrap();

    let mut rt = Runtime::new(ins);

    println!("=====Starting execution=====");
    while let Some(ins) = rt.peek_instruction() {
        println!("{:?} -> {}", rt.registers(), rt.prev_result());
        println!("    {}: {}", rt.instruction_ptr(), ins.to_string_asm(),);
        rt.step().unwrap();
    }
    println!("{:?}", rt.registers());

    // println!("Final state: {rt:#?}");

    Ok(())
}
