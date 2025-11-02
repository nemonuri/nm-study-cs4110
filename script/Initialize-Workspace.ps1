
Set-StrictMode -Version 3.0
$ErrorActionPreference = 'Stop'

$script:root = Join-Path $PSScriptRoot ".." -Resolve

#--- artifact ---
$script:artifact = Join-Path $script:root 'artifact'
if (-not (Test-Path $script:artifact -PathType Container)) {
    New-Item $script:artifact -ItemType Directory
}
#---|