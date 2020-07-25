extern crate piston_window;
use std::env;
use std::fs::File;
use std::io;

mod system;
use piston_window::*;

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

        let scale = 4;
        let mut window: PistonWindow = WindowSettings::new("Gameboy emulator", [160 * scale, 144 * scale]).exit_on_esc(true).build().unwrap();

        while let Some(event) = window.next() {
            match event {
                Event::Input(i, _) => {
                    match i {
                        Input::Button(args) => {
                            match args.button {
                                Button::Keyboard(Key::Right) => {
                                    match args.state {
                                        ButtonState::Press => soc.set_button_right(true),
                                        ButtonState::Release => soc.set_button_right(false)
                                    }
                                }
                                Button::Keyboard(Key::Left) => {
                                    match args.state {
                                        ButtonState::Press => soc.set_button_left(true),
                                        ButtonState::Release => soc.set_button_left(false)
                                    }
                                }
                                Button::Keyboard(Key::Up) => {
                                    match args.state {
                                        ButtonState::Press => soc.set_button_up(true),
                                        ButtonState::Release => soc.set_button_up(false)
                                    }
                                }
                                Button::Keyboard(Key::Down) => {
                                    match args.state {
                                        ButtonState::Press => soc.set_button_down(true),
                                        ButtonState::Release => soc.set_button_down(false)
                                    }
                                }
                                _ => {
                                }
                            }
                        },
                        _ => {
                        }
                    }
                },
                Event::Loop(l) => {
                    match l {
                        Loop::Render(args) => {
                            let screen_data = soc.screen();
                            window.draw_2d(&event, | context, graphics, _device | {
                                clear([0.6; 4], graphics);
                                for y in 0..144 {
                                    for x in 0..160 {
                                        let v = screen_data[160 * y + x];
                                        let c = match v {
                                            0 => [1.0, 1.0, 1.0, 1.0],
                                            1 => [0.666, 0.666, 0.666, 1.0],
                                            2 => [0.333, 0.333, 0.333, 1.0],
                                            3 => [0.0, 0.0, 0.0, 1.0],
                                            _ => unreachable!()
                                        };
                                        let lx = (x as u32 * scale) as f64;
                                        let rx = ((x as u32 + 1) * scale) as f64;
                                        let uy = (y as u32 * scale) as f64;
                                        let dy = ((y as u32 + 1) * scale) as f64;

                                        rectangle(c, [lx, uy, rx, dy], context.transform, graphics)
                                    }
                                }
                            });
                        },
                        Loop::Update(args) => {
                            // FIXME: Remove this "for" when it runs faster than gameboy
                            for _ in 0..40 {
                                soc.step_seconds(args.dt);
                            }
                        }
                        _ => {
                        }
                    }
                },
                Event::Custom(_, _, _) => {
                }
            }
        }

        // loop {
        //     soc.step();
        // }

    } else {
        println!("Usage: {} target.rom", args[0]);
        println!("Usage: {} target.rom gb-bios", args[0]);
        return
    }
}
