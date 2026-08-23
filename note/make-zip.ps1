# Build the arXiv submission zip with spec-compliant forward-slash entry
# names (Compress-Archive writes backslash entries, which some Linux unzip
# tools treat as literal filename characters — arXiv runs on Linux).
# Usage: powershell -File make-zip.ps1 [-Dest C:\temp\fs-lower-bound-arxiv.zip]
param([string]$Dest = "C:\temp\fs-lower-bound-arxiv.zip")

Add-Type -AssemblyName System.IO.Compression.FileSystem
$src = $PSScriptRoot
if (Test-Path $Dest) { Remove-Item $Dest -Force }
New-Item -ItemType Directory -Force (Split-Path $Dest) | Out-Null

$zip = [System.IO.Compression.ZipFile]::Open($Dest, 'Create')
[System.IO.Compression.ZipFileExtensions]::CreateEntryFromFile(
    $zip, "$src\main.tex", "main.tex") | Out-Null
Get-ChildItem "$src\anc" -Recurse -File | ForEach-Object {
    $rel = $_.FullName.Substring($src.Length + 1) -replace '\\', '/'
    [System.IO.Compression.ZipFileExtensions]::CreateEntryFromFile(
        $zip, $_.FullName, $rel) | Out-Null
}
$zip.Dispose()
Write-Host "Wrote $Dest ($((Get-Item $Dest).Length) bytes)"
