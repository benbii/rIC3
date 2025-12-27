use super::engine::{AssertionStatus, PropertyResult, TryProveResult};
use ratatui::crossterm::style::Stylize;
use std::path::Path;
use tabled::{
    settings::{object::Rows, Format, Modify, Style},
    Table, Tabled,
};

#[derive(Tabled)]
struct PropertyRow {
    #[tabled(rename = "Property")]
    property: String,
    #[tabled(rename = "Waveform")]
    waveform: String,
    #[tabled(rename = "Status")]
    status: String,
}

fn status_string(status: &AssertionStatus) -> String {
    match status {
        AssertionStatus::Proved => "Proved".green().to_string(),
        AssertionStatus::HardTransFound => {
            "Hard-to-disprove transitions found".red().to_string()
        }
        AssertionStatus::NotBlocked => "Previous hard transitions not blocked"
            .red()
            .bold()
            .to_string(),
        AssertionStatus::BlockedNewFound => {
            "Previous blocked, new ones found".yellow().to_string()
        }
        AssertionStatus::Triggered => "Assertion triggered".red().bold().to_string(),
    }
}

fn waveform_path(status: &AssertionStatus, vcd_idx: Option<usize>) -> String {
    match status {
        AssertionStatus::Proved => "-".to_string(),
        AssertionStatus::Triggered => "counterexample.vcd".to_string(),
        _ => match vcd_idx {
            Some(idx) => format!("hard_trans/{}.vcd", idx),
            None => "-".to_string(),
        },
    }
}

pub fn print_result(result: &TryProveResult, dut_dir: &Path) {
    // Check if all proved
    let all_proved = result
        .properties
        .iter()
        .all(|p| matches!(p.status, AssertionStatus::Proved));

    if all_proved {
        println!("{}", "All assertions proved.".green());
        return;
    }

    // Check for counterexample
    if let Some(ref cex_path) = result.cex_vcd {
        if let Some(prop) = result.properties.first() {
            println!(
                "{}",
                format!("Counterexample found for {}.", prop.name).red()
            );
            println!("VCD: {}", cex_path.display());
            println!("Your helper assertion may be too strong - it blocks valid states.");
        }
        return;
    }

    // Build VCD index map: prop_id -> vcd_index
    let vcd_map: std::collections::HashMap<usize, usize> = result
        .vcds
        .iter()
        .map(|(idx, _, prop_id)| (*prop_id, *idx))
        .collect();

    // Build table rows
    let rows: Vec<PropertyRow> = result
        .properties
        .iter()
        .map(|p| {
            let vcd_idx = vcd_map.get(&p.id).copied();
            PropertyRow {
                property: p.name.clone(),
                waveform: waveform_path(&p.status, vcd_idx),
                status: status_string(&p.status),
            }
        })
        .collect();

    let mut table = Table::new(&rows);
    table.with(Style::empty()).with(
        Modify::new(Rows::first()).with(Format::content(|s| s.yellow().bold().to_string())),
    );
    println!("{}", table);

    // Print hint
    if !result.vcds.is_empty() {
        println!(
            "\nWaveforms are in: {}",
            dut_dir.join("hard_trans").display()
        );
        println!("Add helper assertions to block the hard transitions shown in waveforms.");
    }
}
