# Shows Windows' "open file" picker on top of everything and prints the chosen
# file, or nothing when cancelled. Used by Game Library's + button (a game's
# .exe or shortcut) and by "Choose image" (a picture for a game).
param([string]$Start = "", [string]$Kind = "game")
$ErrorActionPreference = "Stop"
[Console]::OutputEncoding = [System.Text.Encoding]::UTF8
Add-Type -AssemblyName System.Windows.Forms
# An invisible top-most owner, so the picker opens in front of Fenn.
$owner = New-Object System.Windows.Forms.Form
$owner.TopMost = $true
$owner.ShowInTaskbar = $false
$owner.FormBorderStyle = "None"
$owner.Opacity = 0
$owner.StartPosition = "CenterScreen"
$owner.Size = New-Object System.Drawing.Size(1, 1)
$owner.Show()
$owner.Activate()
try {
    $dialog = New-Object System.Windows.Forms.OpenFileDialog
    if ($Kind -eq "image") {
        $dialog.Title = "Pick a picture for the game"
        $dialog.Filter = "Pictures (*.png;*.jpg;*.jpeg;*.bmp)|*.png;*.jpg;*.jpeg;*.bmp"
    } else {
        $dialog.Title = "Pick the game's .exe (or a shortcut to it)"
        $dialog.Filter = "Games and shortcuts (*.exe;*.lnk)|*.exe;*.lnk|All files (*.*)|*.*"
        $dialog.DereferenceLinks = $false  # keep a shortcut as the shortcut
    }
    $dialog.CheckFileExists = $true
    if ($Start -and (Test-Path $Start)) { $dialog.InitialDirectory = $Start }
    if ($dialog.ShowDialog($owner) -eq [System.Windows.Forms.DialogResult]::OK) {
        [Console]::Out.Write($dialog.FileName)
    }
} finally {
    $owner.Close()
}
