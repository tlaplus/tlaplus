## Adventures In macOS Notarization

Due to [Issue 280](https://github.com/tlaplus/tlaplus/issues/280) we have been code signing the application. Beginning in January, 2020, users of Catalina (macOS 10.15) and later will need have their applications also be 'notarized.'

A Java Program Manager at Microsoft, [wrote a Dummies guide](https://medium.com/@gdams/dummies-guide-to-notarizing-your-runtime-a1e9105b2c21) to notarizing which i attempted to apply to the Toolbox application, all from a Catalina install with XCode 11. Notes from following this, plus "insights" discovered from going wrong in the following and then Googling elsewhere, are below.

### The Results, first

I was able to get the .app notarized successfully with Apple; even after that, inquiring as to its signed status using `spctl` would still state that the app was rejected.

In addition, after running the Toolbox the first time, subsequent queries using `spctl` would then tell me:
```
TLA+ Toolbox.app: a sealed resource is missing or invalid
```

The people at Eclipse are [successfully signing and notarizing 2019-09,](https://bugs.eclipse.org/bugs/show_bug.cgi?id=550135) so signing & notarizing RCPs are possible.

### Signing certificates and passwords

As done in 280, the signing certificates need be installed locally via XCode. Also make sure that you have logged into your account at developer.apple.com and have agreed to all of the latest AppConnect agreements, or you will get a message like
```
1 package(s) were not uploaded because they had problems:
	/var/folders/fn/y4q2v5yx5fd0h7t20ss1qr780000gn/T/9C150E6E-4CD2-4C7C-828B-06B374C4A7ED/org.lamport.tla.toolbox.product.product.itmsp - Error Messages:
		You must first sign the relevant contracts online. (1048)
```
when trying to notarize.

Also, notarizing with Apple requires authentication, of course, during the upload. However, authentication with Apple is now always 2FA; to that extent, you must [generate an app-specific password.](https://support.apple.com/en-us/HT204397)

Once you have an app-specific password, cram it in your KeyChain by doing something like:
```
xcrun altool --store-password-in-keychain-item "AC_PASSWORD" -u "your@apple.id" -p abcd-efgh-ijkl-mnop
```

Now you can refer to it in the KeyChain using an appropriate scheme, which we'll see later.

### The routine

Assuming you have built the Toolbox application change directories to be sitting in the directory containing `TLA+ Toolbox.app`

#### The 'entitlements' file

I cribbed this content from the medium.com article and saved it as 'entitlements.plist'
```
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
    <key>com.apple.security.cs.allow-jit</key>
    <true/>
    <key>com.apple.security.cs.allow-unsigned-executable-memory</key>
    <true/>
    <key>com.apple.security.cs.disable-executable-page-protection</key>
    <true/>
    <key>com.apple.security.cs.allow-dyld-environment-variables</key>
    <true/>
    <key>com.apple.security.cs.disable-library-validation</key>
    <true/>
</dict>
</plist>
```

#### Signing the app

Now i signed the app itself with:
```
codesign --entitlements entitlements.plist --options runtime --timestamp -f -s "Developer ID Application: My Company Name (XXXX)" -v "TLA+ Toolbox.app" --deep
```
verifying the signing at this point shows:
```
loki@apalina Desktop % spctl --verbose=4 --assess --type execute "TLA+ Toolbox.app"
TLA+ Toolbox.app: rejected
source=Unnotarized Developer ID
loki@apalina Desktop % codesign --verify -vvvv "TLA+ Toolbox.app"
TLA+ Toolbox.app: valid on disk
TLA+ Toolbox.app: satisfies its Designated Requirement
loki@apalina Desktop %
```

#### Having Apple notarize the thing

I then ZIP'd up the .app and then handed it over to Apple with (this is where we reference the app-specific password we crammed in the KeyChain):
```
loki@apalina Desktop % xcrun altool --notarize-app --primary-bundle-id "org.lamport.tla.toolbox.product.product" --username "your@apple.id" --password "@keychain:AC_PASSWORD" --file "TLA+ Toolbox.app.zip"
No errors uploading 'TLA+ Toolbox.app.zip'.
RequestUUID = de01d0fe-a88e-44fa-802f-da62ec93e994
loki@apalina Desktop %
```

You can check the status with:
```
loki@apalina Desktop % xcrun altool --notarization-info de01d0fe-a88e-44fa-802f-da62ec93e994 --username "your@apple.id" --password "@keychain:AC_PASSWORD"
No errors getting notarization info.

          Date: 2019-10-30 22:21:36 +0000
          Hash: 18eafe5a64abeef722316df47fb5c1f7249a7943df5bc65dccb5d697d00ba55d
    LogFileURL: https://osxapps-ssl.itunes.apple.com/itunes-assets/Enigma113/v4/72/43/75/72xxx05a68b8c/developer_log.json?accessKey=xxx%3D
   RequestUUID: de01d0fe-a88e-44fa-802f-da62ec93e994
        Status: success
   Status Code: 0
Status Message: Package Approved
loki@apalina Desktop %
```
and the service also sends an email when the process has finished.

#### Done?

At this point, unpacking the ZIP i uploaded and then verifying the signature on the .app shows:
```
loki@apalina Desktop % spctl --verbose=4 --assess --type execute "TLA+ Toolbox.app"
TLA+ Toolbox.app: rejected
source=Notarized Developer ID
loki@apalina Desktop %
```
the app is still rejected, whatever that means; though the submission has been notarized.

There is the notion of stapling (so that this notarization can be seen on machines that have no internet access,) however doing this:
```
loki@apalina Desktop % xcrun stapler staple "TLA+ Toolbox.app"
Processing: /Users/loki/Desktop/TLA+ Toolbox.app
Processing: /Users/loki/Desktop/TLA+ Toolbox.app
The staple and validate action worked!
loki@apalina Desktop % spctl --verbose=4 --assess --type execute "TLA+ Toolbox.app"
TLA+ Toolbox.app: rejected
source=Notarized Developer ID
loki@apalina Desktop %
```
affects nothing obvious concerning the rejection.
