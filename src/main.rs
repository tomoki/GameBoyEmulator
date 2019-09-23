use std::env;
use std::fs::File;
use std::io;

mod system;

fn read_data(filename: &str) -> io::Result<Vec<u8>> {
    use std::io::Read;

    let file = File::open(filename);
    match file {
        Err(why) => Err(why),
        Ok(mut file) => {
            let mut ret: Vec<u8> = Vec::new();
            match file.read_to_end(&mut ret) {
                Err(why) => Err(why),
                Ok(_size) => Ok(ret)
            }
        }
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let mut soc = system::SystemOnChip::new();

    if args.len() >= 2 {
        soc.reset();

        let cartridge_filename = &args[1];
        let mut cartridge_data : Vec<u8> = Vec::new();

        match read_data(cartridge_filename) {
            Err(why) => panic!(why),
            Ok(cart) => {
                cartridge_data = cart;
            }
        }

        soc.load_cart(&cartridge_data);

        if args.len() >= 3 {
            let bios_filename = &args[2];
            let mut bios_data : Vec<u8> = Vec::new();
            match read_data(bios_filename) {
                Err(why) => panic!(why),
                Ok(bios) => {
                    bios_data = bios;
                }
            }
            soc.load_bios(&bios_data);
        }

        loop {
            soc.dispatch();
        }

    } else {
        println!("Usage: {} target.rom", args[0]);
        println!("Usage: {} target.rom gb-bios", args[0]);
        return
    }
}
