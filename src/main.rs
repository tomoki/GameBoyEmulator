extern crate piston_window;
use std::env;
use std::fs::File;
use std::io;

mod system;
use piston_window::*;
use ::image::{RgbaImage, Rgba};

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
        let mut window: PistonWindow = WindowSettings::new("Gameboy emulator", [160 * scale, 144 * scale]).exit_on_esc(true).samples(0).resizable(false).build().unwrap();

        let mut texture_context = TextureContext {
            factory: window.factory.clone(),
            encoder: window.factory.create_command_buffer().into()
        };

        let mut screen_image = RgbaImage::new(160, 144);
        let mut screen_texture = Texture::from_image(
            &mut texture_context,
            &screen_image,
            &TextureSettings::new().filter(piston_window::Filter::Nearest)
        ).unwrap();

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
                                Button::Keyboard(Key::Z) => {
                                    match args.state {
                                        ButtonState::Press => soc.set_button_a(true),
                                        ButtonState::Release => soc.set_button_a(false)
                                    }
                                }
                                Button::Keyboard(Key::X) => {
                                    match args.state {
                                        ButtonState::Press => soc.set_button_b(true),
                                        ButtonState::Release => soc.set_button_b(false)
                                    }
                                }
                                Button::Keyboard(Key::Return) => {
                                    match args.state {
                                        ButtonState::Press => soc.set_button_start(true),
                                        ButtonState::Release => soc.set_button_start(false)
                                    }
                                }
                                Button::Keyboard(Key::Space) => {
                                    match args.state {
                                        ButtonState::Press => soc.set_button_select(true),
                                        ButtonState::Release => soc.set_button_select(false)
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
                            // Update texture data
                            for y in 0..144 {
                                for x in 0..160 {
                                    let v = screen_data[160 * y + x];
                                    let c = match v {
                                        0 => Rgba([255, 255, 255, 255]),
                                        1 => Rgba([170, 170, 170, 255]),
                                        2 => Rgba([85, 85, 85, 255]),
                                        3 => Rgba([0, 0, 0, 255]),
                                        _ => unreachable!()
                                    };
                                    screen_image.put_pixel(x as u32, y as u32, c);
                                }
                            }
                            screen_texture.update(&mut texture_context, &screen_image).unwrap();

                            window.draw_2d(&event, | context, graphics, device | {
                                // Flush all the changes into the texture
                                texture_context.encoder.flush(device);
                                clear([0.6; 4], graphics);
                                image(&screen_texture, context.transform.scale(scale as f64, scale as f64), graphics);
                            });
                        },
                        Loop::Update(args) => {
                            // FIXME: Remove this "for" when it runs faster than gameboy
                            for _ in 0..1 {
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
