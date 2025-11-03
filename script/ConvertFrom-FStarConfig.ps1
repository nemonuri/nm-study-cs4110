using namespace System.IO

[CmdletBinding()]
param (
    [Parameter(Mandatory, Position=0)][FileInfo] $Path
)

Set-StrictMode -Version 3.0
$ErrorActionPreference = 'Stop'

#--- ensure Path ---
if (-not $Path.Exists) {
    throw "File does not exist. (Path = $Path)"
}

[string]$script:endsWithValue = ".fst.config.json"
if (-not $Path.FullName.EndsWith($script:endsWithValue)) {
    throw "File name should ends with $script:endsWithValue. (Path = $Path)"
}
#---|

Get-Content $Path -Raw | ConvertFrom-Json 