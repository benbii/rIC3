use ahash::HashMap;
use serde::{Deserialize, Serialize};
use std::{fs, path::Path};

/// Stores CTI witnesses from the last run for cross-run comparison.
/// This allows detecting whether helper assertions actually blocked previous hard transitions.
#[derive(Serialize, Deserialize, Default, Clone)]
pub struct LastRunState {
    /// Map: property_name -> serialized witness
    pub ctis: HashMap<String, String>,
}

impl LastRunState {
    pub fn load(proj_path: &Path) -> Option<Self> {
        let path = proj_path.join("tryprove/last_run.ron");
        if path.exists() {
            let content = fs::read_to_string(&path).ok()?;
            ron::from_str(&content).ok()
        } else {
            None
        }
    }

    pub fn save(&self, proj_path: &Path) -> anyhow::Result<()> {
        let dir = proj_path.join("tryprove");
        fs::create_dir_all(&dir)?;
        let path = dir.join("last_run.ron");
        fs::write(&path, ron::to_string(self)?)?;
        Ok(())
    }

    pub fn has_ctis(&self) -> bool {
        !self.ctis.is_empty()
    }
}
